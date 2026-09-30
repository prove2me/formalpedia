-- Prove2me | solution 1 for TranscendenceTheory.bivariate_monic_reduction_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T12:27:15.751142+00:00
-- url     : https://prove2.me/submissions/ec64f95d-fe96-4cda-a086-833f416b23d8

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fin.VecNotation

noncomputable section

open Polynomial
open scoped Polynomial

private def weight {R : Type*} [Semiring R] (w : R → ℕ) (p : R[X]) : ℕ :=
  ∑ i ∈ p.support, w (p.coeff i)

private lemma weight_zero {R : Type*} [Semiring R] (w : R → ℕ) :
    weight w (0 : R[X]) = 0 := by simp [weight]

private lemma weight_add {R : Type*} [Semiring R] (w : R → ℕ)
    (hw0 : w 0 = 0) (hwadd : ∀ a b, w (a + b) ≤ w a + w b) (p q : R[X]) :
    weight w (p + q) ≤ weight w p + weight w q := by
  classical
  let t := p.support ∪ q.support
  have heq (r : R[X]) (hr : r.support ⊆ t) :
      weight w r = ∑ i ∈ t, w (r.coeff i) := by
    apply Finset.sum_subset hr
    intro i _ hi
    simp [notMem_support_iff.mp hi, hw0]
  rw [heq _ support_add, heq p Finset.subset_union_left,
    heq q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hwadd _ _

private lemma weight_sum {R ι : Type*} [Semiring R] (w : R → ℕ)
    (hw0 : w 0 = 0) (hwadd : ∀ a b, w (a + b) ≤ w a + w b)
    (s : Finset ι) (f : ι → R[X]) :
    weight w (∑ i ∈ s, f i) ≤ ∑ i ∈ s, weight w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (weight_add w hw0 hwadd _ _).trans (Nat.add_le_add_left ih _)

private lemma weight_monomial {R : Type*} [Semiring R] (w : R → ℕ)
    (hw0 : w 0 = 0) (i : ℕ) (a : R) : weight w (monomial i a) = w a := by
  classical
  by_cases ha : a = 0 <;> simp [weight, support_monomial, ha, hw0]

private lemma weight_mul {R : Type*} [Semiring R] (w : R → ℕ)
    (hw0 : w 0 = 0) (hwadd : ∀ a b, w (a + b) ≤ w a + w b)
    (hwmul : ∀ a b, w (a * b) ≤ w a * w b) (p q : R[X]) :
    weight w (p * q) ≤ weight w p * weight w q := by
  classical
  conv_lhs => rw [← sum_monomial_eq p, ← sum_monomial_eq q]
  simp only [sum_def, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
  apply (weight_sum w hw0 hwadd _ _).trans
  apply (Finset.sum_le_sum fun _ _ => weight_sum w hw0 hwadd _ _).trans
  simp only [weight_monomial w hw0]
  calc
    _ ≤ ∑ j ∈ q.support, ∑ i ∈ p.support, w (p.coeff i) * w (q.coeff j) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hwmul _ _
    _ = weight w p * weight w q := by simp [weight, Finset.mul_sum, Finset.sum_mul]

private lemma weight_neg {R : Type*} [Ring R] (w : R → ℕ)
    (hwneg : ∀ a, w (-a) = w a) (p : R[X]) : weight w (-p) = weight w p := by
  simp [weight, hwneg]

private lemma weight_coeff_le {R : Type*} [Semiring R] (w : R → ℕ)
    (hw0 : w 0 = 0) (p : R[X]) (i : ℕ) : w (p.coeff i) ≤ weight w p := by
  classical
  by_cases hi : i ∈ p.support
  · exact Finset.single_le_sum (f := fun j => w (p.coeff j)) (fun j _ => Nat.zero_le _) hi
  · simp [notMem_support_iff.mp hi, hw0]

private abbrev length1 (p : ℤ[X]) : ℕ := weight Int.natAbs p
private abbrev length2 (p : ℤ[X][X]) : ℕ := weight length1 p

private lemma length1_zero : length1 0 = 0 := weight_zero _
private lemma length1_add (p q : ℤ[X]) : length1 (p + q) ≤ length1 p + length1 q :=
  weight_add _ rfl Int.natAbs_add_le p q
private lemma length1_mul (p q : ℤ[X]) : length1 (p * q) ≤ length1 p * length1 q :=
  weight_mul _ rfl Int.natAbs_add_le (fun a b => (Int.natAbs_mul a b).le) p q
private lemma length1_neg (p : ℤ[X]) : length1 (-p) = length1 p :=
  weight_neg _ Int.natAbs_neg p

private lemma length2_zero : length2 0 = 0 := weight_zero _
private lemma length2_add (p q : ℤ[X][X]) : length2 (p + q) ≤ length2 p + length2 q :=
  weight_add _ length1_zero length1_add p q
private lemma length2_mul (p q : ℤ[X][X]) : length2 (p * q) ≤ length2 p * length2 q :=
  weight_mul _ length1_zero length1_add length1_mul p q
private lemma length2_sub (p q : ℤ[X][X]) : length2 (p - q) ≤ length2 p + length2 q := by
  simpa [sub_eq_add_neg, weight_neg _ length1_neg] using length2_add p (-q)

private lemma remainder_bounds (g : ℤ[X][X]) (hg : g.Monic) (B : ℕ)
    (hB : ∀ i, (g.coeff i).natDegree ≤ B) (p : ℤ[X][X]) (A : ℕ)
    (hA : ∀ i, (p.coeff i).natDegree ≤ A) :
    (∀ i, ((p %ₘ g).coeff i).natDegree ≤ A + p.natDegree * B) ∧
    length2 (p %ₘ g) ≤ length2 p * (1 + length2 g) ^ (p.natDegree + 1) := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p A with
  | h n ih =>
    rw [← hn]
    by_cases hp : p = 0
    · subst p
      simp [length2_zero]
    by_cases hd : g.degree ≤ p.degree
    · let r := p - g * (C p.leadingCoeff * X ^ (p.natDegree - g.natDegree))
      have hrmod : r %ₘ g = p %ₘ g := by
        simp [r, sub_modByMonic, self_mul_modByMonic hg]
      have hrA : ∀ i, (r.coeff i).natDegree ≤ A + B := by
        intro i
        apply (natDegree_sub_le _ _).trans
        refine max_le (le_trans (hA i) (Nat.le_add_right _ _)) ?_
        change (coeff (g * (C p.leadingCoeff * X ^ _)) i).natDegree ≤ A + B
        rw [← mul_assoc, coeff_mul_X_pow']
        split_ifs
        · rw [coeff_mul_C]
          exact (natDegree_mul_le).trans (by
            have := Nat.add_le_add (hB (i - (p.natDegree - g.natDegree))) (hA p.natDegree)
            simpa only [leadingCoeff, add_comm B A] using this)
        · simp
      have hrlen : length2 r ≤ length2 p * (1 + length2 g) := by
        apply (length2_sub _ _).trans
        have hc : length2 (C p.leadingCoeff * X ^ (p.natDegree - g.natDegree)) =
            length1 p.leadingCoeff := by
          rw [C_mul_X_pow_eq_monomial]
          exact weight_monomial _ length1_zero _ _
        have hl := weight_coeff_le length1 length1_zero p p.natDegree
        calc
          _ ≤ length2 p + length2 g * length1 p.leadingCoeff := by
            exact Nat.add_le_add_left ((length2_mul _ _).trans_eq (by rw [hc])) _
          _ ≤ length2 p + length2 g * length2 p :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
          _ = _ := by ring
      rw [← hrmod]
      by_cases hr : r = 0
      · simp [hr, length2_zero]
      have hdeg : r.natDegree < p.natDegree :=
        natDegree_lt_natDegree hr (div_wf_lemma ⟨hd, hp⟩ hg)
      obtain ⟨hdegR, hlenR⟩ := ih r.natDegree (by omega) r (A + B) hrA rfl
      constructor
      · intro i
        apply (hdegR i).trans
        calc
          A + B + r.natDegree * B = A + (r.natDegree + 1) * B := by ring
          _ ≤ A + p.natDegree * B := Nat.add_le_add_left (Nat.mul_le_mul_right B hdeg) A
      · apply hlenR.trans
        calc
          _ ≤ (length2 p * (1 + length2 g)) * (1 + length2 g) ^ (r.natDegree + 1) :=
            Nat.mul_le_mul_right _ hrlen
          _ = length2 p * (1 + length2 g) ^ (r.natDegree + 2) := by
            rw [pow_succ, ← mul_assoc]
            ring
          _ ≤ length2 p * (1 + length2 g) ^ (p.natDegree + 1) := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) (by omega)
    · rw [(modByMonic_eq_self_iff hg).mpr (lt_of_not_ge hd)]
      exact ⟨fun i => (hA i).trans (Nat.le_add_right _ _),
        Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)⟩

private def toBivariate (p : MvPolynomial (Fin 2) ℤ) : ℤ[X][X] :=
  ∑ m ∈ p.support, monomial (m 1) (monomial (m 0) (p.coeff m))

private lemma toBivariate_bounds (p : MvPolynomial (Fin 2) ℤ) :
    (toBivariate p).natDegree ≤ p.totalDegree ∧
    (∀ i, ((toBivariate p).coeff i).natDegree ≤ p.totalDegree) ∧
    length2 (toBivariate p) ≤ ∑ m ∈ p.support, (p.coeff m).natAbs := by
  classical
  have hm (m : Fin 2 →₀ ℕ) (h : m ∈ p.support) (i : Fin 2) : m i ≤ p.totalDegree :=
    (MvPolynomial.le_degreeOf_of_mem_support i h).trans (p.degreeOf_le_totalDegree i)
  constructor
  · apply natDegree_sum_le_of_forall_le
    intro m h
    exact (natDegree_monomial_le _).trans (hm m h 1)
  constructor
  · intro i
    simp only [toBivariate, finsetSum_coeff]
    apply natDegree_sum_le_of_forall_le
    intro m h
    rw [coeff_monomial]
    split_ifs
    · exact (natDegree_monomial_le _).trans (hm m h 0)
    · simp
  · apply (weight_sum length1 length1_zero length1_add _ _).trans_eq
    apply Finset.sum_congr rfl
    intro m _
    rw [weight_monomial length1 length1_zero]
    exact weight_monomial Int.natAbs rfl _ _

private lemma eval_toBivariate (p : MvPolynomial (Fin 2) ℤ)
    {A : Type} [CommRing A] (φ : ℤ[X] →+* A) (y : A) :
    (toBivariate p).eval₂ φ y =
      MvPolynomial.eval₂ (Int.castRingHom A) ![φ X, y] p := by
  classical
  rw [toBivariate, eval₂_finsetSum, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro m _
  have hC (a : ℤ) : φ (C a) = (a : A) := by
    rw [show C a = (a : ℤ[X]) by simp, map_intCast]
  rw [eval₂_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, hC]
  simp [Fin.prod_univ_two, mul_assoc]

/-- Quantitative reduction of an integer bivariate polynomial modulo a monic relation. -/
theorem solution (g : ℤ[X][X]) (hg : g.Monic)
    (hg_degree : 0 < g.natDegree) (B : ℕ)
    (hB : ∀ i, (g.coeff i).natDegree ≤ B) (p : MvPolynomial (Fin 2) ℤ) :
    ∃ r : ℤ[X][X],
      r.natDegree < g.natDegree ∧
      (∀ i, (r.coeff i).natDegree ≤ (B + 1) * p.totalDegree) ∧
      (∑ i ∈ r.support, ∑ j ∈ (r.coeff i).support, ((r.coeff i).coeff j).natAbs) ≤
        (∑ m ∈ p.support, (p.coeff m).natAbs) *
          (1 + ∑ i ∈ g.support, ∑ j ∈ (g.coeff i).support,
            ((g.coeff i).coeff j).natAbs) ^ (p.totalDegree + 1) ∧
      ∀ (A : Type) [CommRing A] (φ : ℤ[X] →+* A) (y : A),
        g.eval₂ φ y = 0 →
        r.eval₂ φ y = MvPolynomial.eval₂ (Int.castRingHom A) ![φ X, y] p := by
  classical
  obtain ⟨hY, hX, hlen⟩ := toBivariate_bounds p
  obtain ⟨hRX, hRlen⟩ := remainder_bounds g hg B hB (toBivariate p) p.totalDegree hX
  refine ⟨toBivariate p %ₘ g, natDegree_modByMonic_lt _ hg ?_, ?_, ?_, ?_⟩
  · intro h
    simp [h] at hg_degree
  · intro i
    apply (hRX i).trans
    calc
      _ ≤ p.totalDegree + p.totalDegree * B :=
        Nat.add_le_add_left (Nat.mul_le_mul_right B hY) _
      _ = _ := by ring
  · apply hRlen.trans
    exact Nat.mul_le_mul hlen (Nat.pow_le_pow_right (by omega) (by omega))
  · intro A _ φ y hy
    rw [eval₂_modByMonic_eq_self_of_root hy, eval_toBivariate]

