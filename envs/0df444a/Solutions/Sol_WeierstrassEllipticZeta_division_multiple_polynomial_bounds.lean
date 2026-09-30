-- Prove2me | solution 1 for WeierstrassEllipticZeta.division_multiple_polynomial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T18:49:37.337279+00:00
-- url     : https://prove2.me/submissions/6373d43e-830f-42aa-92f3-713013d482b6

import Definitions.Def_WeierstrassEllipticZeta_DivisionPolynomials
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring

noncomputable section

open MvPolynomial

namespace TranscendenceTheory

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma derivation_length {σ : Type}
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (H : ℕ) (hH : ∀ i, polyLength (D (X i)) ≤ H)
    (p : MvPolynomial σ ℤ) :
    polyLength (D p) ≤ H * p.totalDegree * polyLength p := by
  classical
  have hD : D = mkDerivation ℤ (fun i => D (X i)) := by
    apply derivation_ext
    intro i
    simp
  have hmon (m : σ →₀ ℕ) (a : ℤ) :
      polyLength (D (monomial m a)) ≤ H * (m.sum fun _ k => k) * a.natAbs := by
    rw [hD, mkDerivation_monomial]
    simp only [Finsupp.sum, Finset.smul_sum, smul_eq_mul, ← C_mul',
      ← mul_assoc, C_mul_monomial]
    apply (polyLength_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ m.support, (a.natAbs * m i) * H := by
        apply Finset.sum_le_sum
        intro i _
        apply (polyLength_mul _ _).trans
        simpa only [polyLength_monomial, Int.natAbs_mul, Int.natAbs_natCast] using
          Nat.mul_le_mul_left (a.natAbs * m i) (hH i)
      _ = _ := by simp only [← Finset.sum_mul, ← Finset.mul_sum]; ring
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply (polyLength_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, H * p.totalDegree * (p.coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m hm
      exact (hmon m _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left H
        (le_totalDegree hm)))
    _ = _ := by rw [← Finset.mul_sum]; rfl

private lemma pderiv_degree {σ : Type} (p : MvPolynomial σ ℤ) (i : σ)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, heq⟩ := (pderiv i p).support.exists_mem_eq_sup
    (by simpa using h) (fun m => m.sum fun _ e => e)
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have := mem_support_iff.mp hm
    rw [coeff_pderiv] at this
    exact (mul_ne_zero_iff.mp this).1
  have hle := le_totalDegree (mem_support_iff.mpr hcoeff)
  simpa [totalDegree, heq, Finsupp.sum_add_index'] using hle

private lemma derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (p : MvPolynomial σ ℤ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma derivation_degree {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2) (p : MvPolynomial σ ℤ) :
    (D p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  have hrepr : D = ∑ i, D (X i) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ i, D (X i) * pderiv i p := by
    conv_lhs => rw [hrepr]
    simp [derivation_sum_apply]
  rw [hvalue]
  apply totalDegree_finsetSum_le
  intro i _
  by_cases hi : pderiv i p = 0
  · simp [hi]
  have hp := pderiv_degree p i hi
  have hmul := totalDegree_mul (D (X i)) (pderiv i p)
  have := hD i
  omega


private lemma iterated_length {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (H : ℕ) (hH : ∀ i, polyLength (D (X i)) ≤ H)
    (p : MvPolynomial σ ℤ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
    polyLength (D^[n] p) ≤
      polyLength p * H ^ n * (p.totalDegree + 1).ascFactorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact (derivation_degree D hD _).trans (by omega)
    · apply (derivation_length D H hH _).trans
      calc
        _ ≤ H * (p.totalDegree + 1 + n) *
            (polyLength p * H ^ n * (p.totalDegree + 1).ascFactorial n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left H (by omega)) ih.2
        _ = _ := by rw [Nat.ascFactorial_succ, pow_succ]; ring

/-- Quadratic integer polynomial derivations have factorial-exponential
coefficient-length growth, uniformly in the derivative order. -/
theorem polynomial_derivation_length_bound {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (H : ℕ) (hHpos : 1 ≤ H)
    (hH : ∀ i, (∑ m ∈ (D (X i)).support, ((D (X i)).coeff m).natAbs) ≤ H)
    (p : MvPolynomial σ ℤ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
    (∑ m ∈ (D^[n] p).support, ((D^[n] p).coeff m).natAbs) ≤
      (∑ m ∈ p.support, (p.coeff m).natAbs) * n.factorial *
        (2 * H) ^ (p.totalDegree + n) := by
  obtain ⟨hdeg, hlen⟩ := iterated_length D hD H hH p n
  refine ⟨hdeg, hlen.trans ?_⟩
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  calc
    _ ≤ polyLength p * H ^ (p.totalDegree + n) *
        (n.factorial * 2 ^ (p.totalDegree + n)) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hHpos (by omega)))
        (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _))
    _ = _ := by rw [mul_pow]; unfold polyLength; ring

end TranscendenceTheory

noncomputable section
open MvPolynomial
open WeierstrassEllipticZeta

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma polyLength_one {τ : Type} : polyLength (1 : MvPolynomial τ ℤ) = 1 := by
  exact polyLength_monomial (0 : τ →₀ ℕ) 1

private lemma polyLength_C {τ : Type} (a : ℤ) :
    polyLength (C a : MvPolynomial τ ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_pow {τ : Type} (p : MvPolynomial τ ℤ) (n : ℕ) :
    polyLength (p ^ n) ≤ polyLength p ^ n := by
  induction n with
  | zero => simp [polyLength_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma polyLength_prod {τ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial τ ℤ) :
    polyLength (∏ i ∈ s, f i) ≤ ∏ i ∈ s, polyLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyLength_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_left _ ih)

private lemma polyLength_add {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p + q) ≤ polyLength p + polyLength q := by
  simpa [Fin.sum_univ_succ] using polyLength_sum_le (Finset.univ : Finset (Fin 2)) ![p, q]

private lemma polyLength_neg {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength (-p) = polyLength p := by simp [polyLength]

private lemma polyLength_sub {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p - q) ≤ polyLength p + polyLength q := by
  simpa only [sub_eq_add_neg, polyLength_neg] using polyLength_add p (-q)

private lemma polyLength_X {σ : Type} (j : σ) :
    polyLength (X j : MvPolynomial σ ℤ) = 1 := polyLength_monomial _ 1


private def Growth {σ : Type} (D H : ℕ) (p : MvPolynomial σ ℤ) (e : ℕ) : Prop :=
  p.totalDegree ≤ D * e ∧ polyLength p ≤ H ^ e

private lemma growth_mono {σ : Type} {D H : ℕ} (hH : 1 ≤ H)
    {p : MvPolynomial σ ℤ} {e f : ℕ} (hp : Growth D H p e) (hef : e ≤ f) :
    Growth D H p f :=
  ⟨hp.1.trans (Nat.mul_le_mul_left _ hef),
    hp.2.trans (Nat.pow_le_pow_right hH hef)⟩

private lemma growth_mul {σ : Type} {D H : ℕ} {p q : MvPolynomial σ ℤ} {e f : ℕ}
    (hp : Growth D H p e) (hq : Growth D H q f) : Growth D H (p * q) (e + f) := by
  constructor
  · exact (totalDegree_mul _ _).trans (by nlinarith [hp.1, hq.1])
  · simpa [pow_add] using (polyLength_mul _ _).trans (Nat.mul_le_mul hp.2 hq.2)

private lemma growth_pow {σ : Type} {D H : ℕ} {p : MvPolynomial σ ℤ} {e : ℕ}
    (hp : Growth D H p e) (n : ℕ) : Growth D H (p ^ n) (n * e) := by
  constructor
  · exact (totalDegree_pow _ _).trans (by nlinarith [hp.1])
  · simpa [pow_mul, Nat.mul_comm] using
      (polyLength_pow _ _).trans (Nat.pow_le_pow_left hp.2 n)

private lemma growth_one {σ : Type} (D H : ℕ) :
    Growth D H (1 : MvPolynomial σ ℤ) 0 := by simp [Growth, polyLength_one]

private lemma growth_sub {σ : Type} {D H : ℕ} (hH : 2 ≤ H)
    {p q : MvPolynomial σ ℤ} {e f : ℕ}
    (hp : Growth D H p e) (hq : Growth D H q f) :
    Growth D H (p - q) (max e f + 1) := by
  have hH1 : 1 ≤ H := by omega
  have hp' := growth_mono hH1 hp (Nat.le_max_left e f)
  have hq' := growth_mono hH1 hq (Nat.le_max_right e f)
  constructor
  · exact (totalDegree_sub _ _).trans
      ((max_le hp'.1 hq'.1).trans (Nat.mul_le_mul_left D (by omega)))
  · exact (polyLength_sub _ _).trans ((Nat.add_le_add hp'.2 hq'.2).trans (by
      rw [pow_succ]
      simpa [mul_two] using Nat.mul_le_mul_left (H ^ max e f) hH))

private lemma recurrence_even_exponents (m : ℕ) :
    max (2 * ((m + 2) ^ 2 - 3) + ((m + 3) ^ 2 - 3) + ((m + 5) ^ 2 - 3))
      (((m + 1) ^ 2 - 3) + ((m + 3) ^ 2 - 3) + 2 * ((m + 4) ^ 2 - 3)) + 1 ≤
        (2 * (m + 3)) ^ 2 - 3 := by
  rw [← max_add_add_right]
  apply max_le
  · ring_nf
    omega
  · cases m with
    | zero => norm_num
    | succ m => ring_nf; omega

private lemma recurrence_odd_exponents (m : ℕ) :
    max (((m + 4) ^ 2 - 3) + 3 * ((m + 2) ^ 2 - 3) + 1)
      (((m + 1) ^ 2 - 3) + 3 * ((m + 3) ^ 2 - 3) + 1) + 1 ≤
        (2 * (m + 2) + 1) ^ 2 - 3 := by
  rw [← max_add_add_right]
  apply max_le
  · ring_nf
    omega
  · cases m with
    | zero => norm_num
    | succ m => ring_nf; omega

private theorem preEDS_growth {σ : Type} (b c d : MvPolynomial σ ℤ)
    (D H : ℕ) (hH : 2 ≤ H) (hb : Growth D H b 1)
    (hc : Growth D H c 1) (hd : Growth D H d 1) (n : ℕ) :
    Growth D H (preNormEDS' b c d n) (n ^ 2 - 3) := by
  have hH1 : 1 ≤ H := by omega
  induction n using normEDSRec' with
  | zero => simp [Growth, polyLength]
  | one => simpa using growth_one (σ := σ) D H
  | two => simpa using growth_mono hH1 (growth_one (σ := σ) D H) (show 0 ≤ 1 by omega)
  | three => simpa using growth_mono hH1 hc (show 1 ≤ 6 by omega)
  | four => simpa using growth_mono hH1 hd (show 1 ≤ 13 by omega)
  | even m ih =>
    rw [preNormEDS'_even]
    exact growth_mono hH1 (growth_sub hH
      (growth_mul (growth_mul (growth_pow (ih _ (by omega)) 2) (ih _ (by omega)))
        (ih _ (by omega)))
      (growth_mul (growth_mul (ih _ (by omega)) (ih _ (by omega)))
        (growth_pow (ih _ (by omega)) 2))) (recurrence_even_exponents m)
  | odd m ih =>
    rw [preNormEDS'_odd]
    have hb₁ : Growth D H (if Even m then b else 1) 1 := by
      split_ifs
      · exact hb
      · exact growth_mono hH1 (growth_one D H) (by omega)
    have hb₂ : Growth D H (if Even m then 1 else b) 1 := by
      split_ifs
      · exact growth_mono hH1 (growth_one D H) (by omega)
      · exact hb
    exact growth_mono hH1 (growth_sub hH
      (growth_mul (growth_mul (ih _ (by omega)) (growth_pow (ih _ (by omega)) 3)) hb₁)
      (growth_mul (growth_mul (ih _ (by omega)) (growth_pow (ih _ (by omega)) 3)) hb₂))
        (recurrence_odd_exponents m)


private lemma growth_add {σ : Type} {D H : ℕ} (hH : 2 ≤ H)
    {p q : MvPolynomial σ ℤ} {e f : ℕ}
    (hp : Growth D H p e) (hq : Growth D H q f) :
    Growth D H (p + q) (max e f + 1) := by
  have hn : Growth D H (-q) f := by simpa [Growth, polyLength_neg] using hq
  simpa using growth_sub hH hp hn

private lemma division_polynomial_growth : ∃ D H : ℕ, 0 < D ∧ 2 ≤ H ∧ ∀ n : ℕ,
    Growth D H (ellipticDivisionPolynomial n) (n ^ 2) := by
  let D := 1 + ellipticDivisionB.totalDegree + ellipticDivisionC.totalDegree +
    ellipticDivisionD.totalDegree
  let H := 2 + polyLength ellipticDivisionB + polyLength ellipticDivisionC +
    polyLength ellipticDivisionD
  have hD : 0 < D := by dsimp [D]; omega
  have hH : 2 ≤ H := by dsimp [H]; omega
  have hH1 : 1 ≤ H := by omega
  have hb : Growth D H ellipticDivisionB 1 := by
    constructor <;> simp only [mul_one, pow_one] <;> dsimp [D, H] <;> omega
  have hc : Growth D H ellipticDivisionC 1 := by
    constructor <;> simp only [mul_one, pow_one] <;> dsimp [D, H] <;> omega
  have hd : Growth D H ellipticDivisionD 1 := by
    constructor <;> simp only [mul_one, pow_one] <;> dsimp [D, H] <;> omega
  refine ⟨D, H, hD, hH, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, ellipticDivisionPolynomial, Growth, polyLength]
  have hx : Growth D H (if Even n then X 3 else 1 : MvPolynomial (Fin 5) ℤ) 1 := by
    split_ifs
    · constructor
      · simpa only [totalDegree_X, mul_one] using (show 1 ≤ D by omega)
      · simpa [polyLength_X] using hH1
    · exact growth_mono hH1 (growth_one D H) (by omega)
  exact growth_mono hH1 (growth_mul (preEDS_growth _ _ _ D H hH hb hc hd n) hx)
    (by have : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n (by omega); omega)

private lemma multiple_derivation_bounds :
    (∀ i, (ellipticMultipleDerivation (X i)).totalDegree ≤ 2) ∧
    (∀ i, polyLength (ellipticMultipleDerivation (X i)) ≤ 8) := by
  have hdeg : (C (6 : ℤ) * (X (2 : Fin 5)) ^ 2 - C 2 * X 0).totalDegree ≤ 2 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact (totalDegree_pow _ _).trans (by simp only [totalDegree_X]; omega)
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X]; omega)
  have hlen : polyLength (C (6 : ℤ) * (X (2 : Fin 5)) ^ 2 - C 2 * X 0) ≤ 8 := by
    have h₁ := (polyLength_mul (C (6 : ℤ)) (X (2 : Fin 5) ^ 2)).trans
      (Nat.mul_le_mul_left _ (polyLength_pow (X (2 : Fin 5)) 2))
    have h₂ := polyLength_mul (C (2 : ℤ)) (X (0 : Fin 5))
    have h₃ := polyLength_sub (C (6 : ℤ) * (X (2 : Fin 5)) ^ 2) (C 2 * X 0)
    simp only [polyLength_C, polyLength_X, one_pow, mul_one] at h₁ h₂
    omega
  constructor
  · intro i
    simp only [ellipticMultipleDerivation, mkDerivation_X]
    fin_cases i
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact (totalDegree_X _).le.trans (by omega)
    · exact hdeg
    · change (-X (2 : Fin 5) : MvPolynomial (Fin 5) ℤ).totalDegree ≤ 2
      rw [totalDegree_neg, totalDegree_X]
      omega
  · intro i
    simp only [ellipticMultipleDerivation, mkDerivation_X]
    fin_cases i
    · change polyLength (0 : MvPolynomial (Fin 5) ℤ) ≤ 8
      simp [polyLength]
    · change polyLength (0 : MvPolynomial (Fin 5) ℤ) ≤ 8
      simp [polyLength]
    · exact (polyLength_X (3 : Fin 5)).le.trans (by omega)
    · exact hlen
    · change polyLength (-X (2 : Fin 5)) ≤ 8
      rw [polyLength_neg, polyLength_X]
      omega

private lemma division_and_derivative_growth :
    ∃ D H : ℕ, 0 < D ∧ 2 ≤ H ∧
      (∀ n : ℕ, Growth D H (ellipticDivisionPolynomial n) (n ^ 2)) ∧
      (∀ n : ℕ, 0 < n → Growth D H
        (ellipticMultipleDerivation (ellipticDivisionPolynomial n)) (n ^ 2)) := by
  obtain ⟨D, H, hD, hH, hf⟩ := division_polynomial_growth
  let J := H * 16 ^ (D + 1)
  have hHJ : H ≤ J := by
    dsimp [J]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hJ : 2 ≤ J := hH.trans hHJ
  have hF (n : ℕ) : Growth (D + 1) J (ellipticDivisionPolynomial n) (n ^ 2) := by
    exact ⟨(hf n).1.trans (Nat.mul_le_mul_right _ (by omega)),
      (hf n).2.trans (Nat.pow_le_pow_left hHJ _)⟩
  refine ⟨D + 1, J, by omega, hJ, hF, ?_⟩
  intro n hn
  have hn2 : 1 ≤ n ^ 2 := pow_pos hn _
  have hh := TranscendenceTheory.polynomial_derivation_length_bound
    ellipticMultipleDerivation multiple_derivation_bounds.1 8 (by omega)
    multiple_derivation_bounds.2 (ellipticDivisionPolynomial n) 1
  simp only [Function.iterate_one, Nat.factorial_one, mul_one, Nat.reduceMul] at hh
  constructor
  · exact hh.1.trans (by nlinarith [(hf n).1])
  · have hpow : (ellipticDivisionPolynomial n).totalDegree + 1 ≤ (D + 1) * n ^ 2 :=
      by nlinarith [(hf n).1]
    calc
      _ ≤ polyLength (ellipticDivisionPolynomial n) *
          16 ^ ((ellipticDivisionPolynomial n).totalDegree + 1) := hh.2
      _ ≤ H ^ (n ^ 2) * 16 ^ ((D + 1) * n ^ 2) :=
        Nat.mul_le_mul (hf n).2 (Nat.pow_le_pow_right (by omega) hpow)
      _ = J ^ (n ^ 2) := by simp only [J, mul_pow, pow_mul]

private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    omega

/-- The explicit division-polynomial multiplication numerators and denominator
have degree and logarithmic coefficient length bounded quadratically in the index. -/
theorem solution : ∃ C H : ℕ, 0 < C ∧ 0 < H ∧
    ∀ n : ℕ, 0 < n →
      (ellipticDivisionDenominator n).totalDegree ≤ C * n ^ 2 ∧
      (∑ m ∈ (ellipticDivisionDenominator n).support,
        ((ellipticDivisionDenominator n).coeff m).natAbs) ≤ H ^ (n ^ 2) ∧
      (∀ j, (ellipticDivisionNumerator n j).totalDegree ≤ C * n ^ 2) ∧
      (∀ j, (∑ m ∈ (ellipticDivisionNumerator n j).support,
        ((ellipticDivisionNumerator n j).coeff m).natAbs) ≤ H ^ (n ^ 2)) := by
  obtain ⟨D, H, hD, hH, hf, hdf⟩ := division_and_derivative_growth
  have hH1 : 1 ≤ H := by omega
  refine ⟨9 * D, H ^ 9, by positivity, by positivity, ?_⟩
  intro n hn
  have hn2 : 1 ≤ n ^ 2 := pow_pos hn _
  have hC : Growth D H (C (n : ℤ) : MvPolynomial (Fin 5) ℤ) (n ^ 2) := by
    constructor
    · simp only [totalDegree_C]; omega
    · simp only [polyLength_C, Int.natAbs_natCast]
      exact (nat_le_two_pow n).trans ((Nat.pow_le_pow_right (by omega) (by nlinarith)).trans
        (Nat.pow_le_pow_left hH _))
  have hC2 : Growth D H (C ((n : ℤ) ^ 2) : MvPolynomial (Fin 5) ℤ) (n ^ 2) := by
    constructor
    · simp only [totalDegree_C]; omega
    · simp only [polyLength_C, Int.natAbs_pow, Int.natAbs_natCast]
      exact (nat_le_two_pow (n ^ 2)).trans (Nat.pow_le_pow_left hH _)
  have hx (i : Fin 5) : Growth D H (X i) (n ^ 2) := by
    constructor
    · simp only [totalDegree_X]
      exact Nat.mul_pos hD (by omega)
    · simp only [polyLength_X]
      exact Nat.one_le_pow _ _ hH1
  have hm : Growth D H (ellipticDivisionPolynomial (n - 1)) (n ^ 2) :=
    growth_mono hH1 (hf _) (Nat.pow_le_pow_left (Nat.sub_le n 1) 2)
  have hp : Growth D H (ellipticDivisionPolynomial (n + 1)) (4 * n ^ 2) :=
    growth_mono hH1 (hf _) (by nlinarith)
  have ht : Growth D H (ellipticDivisionPolynomial (2 * n)) (4 * n ^ 2) := by
    simpa [mul_pow] using hf (2 * n)
  have hd : Growth D H (ellipticDivisionDenominator n) (9 * n ^ 2) :=
    growth_mono hH1 (growth_mul hC (growth_pow (hf n) 4)) (by omega)
  have hnum : ∀ j, Growth D H (ellipticDivisionNumerator n j) (9 * n ^ 2) := by
    intro j
    fin_cases j
    · exact growth_mono hH1 (growth_add hH
        (growth_mul (growth_mul hC2 (growth_pow (hf n) 4)) (hx 4))
        (growth_mul (growth_pow (hf n) 3) (hdf n hn))) (by omega)
    · exact growth_mono hH1 (growth_mul (growth_mul hC (growth_sub hH
        (growth_mul (hx 2) (growth_pow (hf n) 2)) (growth_mul hm hp)))
        (growth_pow (hf n) 2)) (by omega)
    · exact growth_mono hH1 (growth_mul hC ht) (by omega)
  have hconv (p : MvPolynomial (Fin 5) ℤ) (hh : Growth D H p (9 * n ^ 2)) :
      p.totalDegree ≤ 9 * D * n ^ 2 ∧ polyLength p ≤ (H ^ 9) ^ (n ^ 2) := by
    simpa only [Growth, ← pow_mul, Nat.mul_left_comm D 9, Nat.mul_assoc] using hh
  exact ⟨(hconv _ hd).1, (hconv _ hd).2, fun j => (hconv _ (hnum j)).1,
    fun j => (hconv _ (hnum j)).2⟩

