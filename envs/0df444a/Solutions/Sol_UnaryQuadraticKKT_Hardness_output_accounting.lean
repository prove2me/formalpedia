-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.output_accounting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:15:12.72309+00:00
-- url     : https://prove2.me/submissions/847d186c-28e8-4447-8f61-e0bbcb20d519

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output

set_option autoImplicit false

open MvPolynomial Finset

namespace UQ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- explicit integer quadratic form `c + Σ l_a X_a + Σ_{a,b} q_{ab} X_a X_b`. -/
structure QF (ι : Type) where
  c : ℤ
  l : ι → ℤ
  q : ι → ι → ℤ

noncomputable def QF.toMv (F : QF ι) : MvPolynomial ι ℤ :=
  C F.c + ∑ a, C (F.l a) * X a + ∑ a, ∑ b, C (F.q a b) * X a * X b

theorem coeff_XX (a b : ι) (m : ι →₀ ℕ) :
    coeff m (X a * X b : MvPolynomial ι ℤ) = if m = Finsupp.single a 1 + Finsupp.single b 1 then 1 else 0 := by
  rw [X, X, monomial_mul, coeff_monomial]
  by_cases h : m = Finsupp.single a 1 + Finsupp.single b 1
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coeff_X1 (a : ι) (m : ι →₀ ℕ) :
    coeff m (X a : MvPolynomial ι ℤ) = if m = Finsupp.single a 1 then 1 else 0 := by
  rw [MvPolynomial.coeff_X']; simp [eq_comm]

theorem coeff_toMv (F : QF ι) (m : ι →₀ ℕ) :
    coeff m F.toMv = (if m = 0 then F.c else 0) +
      (∑ a, if m = Finsupp.single a 1 then F.l a else 0) +
      ∑ a, ∑ b, if m = Finsupp.single a 1 + Finsupp.single b 1 then F.q a b else 0 := by
  unfold QF.toMv
  simp only [coeff_add, coeff_sum, coeff_C, mul_assoc, coeff_C_mul, coeff_XX, coeff_X1]
  congr 1
  · congr 1
    · simp [eq_comm]
    · exact sum_congr rfl fun a _ => by split_ifs <;> simp
  · exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by split_ifs <;> simp

end UQ

namespace UQ
open MvPolynomial Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- sparse affine form `c + Σ w X_i`. -/
structure Aff (ι : Type) where
  c : ℤ
  terms : List (ι × ℤ)

def Aff.l (A : Aff ι) (a : ι) : ℤ := ((A.terms.filter fun t => t.1 = a).map Prod.snd).sum

noncomputable def Aff.toMv (A : Aff ι) : MvPolynomial ι ℤ :=
  C A.c + (A.terms.map fun t => C t.2 * X t.1).sum

theorem Aff.toMv_eq (A : Aff ι) : A.toMv = C A.c + ∑ a, C (A.l a) * X a := by
  unfold Aff.toMv Aff.l
  congr 1
  obtain ⟨c, ts⟩ := A
  simp only
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have hl : ∀ a, ((List.filter (fun t' => decide (t'.1 = a)) (t :: ts)).map Prod.snd).sum =
        (if t.1 = a then t.2 else 0) + ((List.filter (fun t' => decide (t'.1 = a)) ts).map Prod.snd).sum := by
      intro a
      by_cases h : t.1 = a <;> simp [List.filter_cons, h]
    have key : ∑ a, C ((List.filter (fun t' => decide (t'.1 = a)) (t :: ts)).map Prod.snd).sum * X a =
        C t.2 * X t.1 + ∑ a, C ((List.filter (fun t' => decide (t'.1 = a)) ts).map Prod.snd).sum * X a := by
      rw [Finset.sum_congr rfl fun a _ => by rw [hl a, C_add, add_mul], Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single t.1]
      · simp
      · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
      · simp
    rw [key]

/-- product of two affine forms as a quadratic form. -/
def mulQF (A B : Aff ι) : QF ι :=
  ⟨A.c * B.c, fun a => A.c * B.l a + B.c * A.l a, fun a b => A.l a * B.l b⟩

theorem toMv_mul (A B : Aff ι) : A.toMv * B.toMv = (mulQF A B).toMv := by
  rw [A.toMv_eq, B.toMv_eq]
  unfold mulQF QF.toMv
  simp only
  have e1 : (∑ a, C (A.l a) * X a) * (∑ b, C (B.l b) * X b) =
      ∑ a, ∑ b, C (A.l a * B.l b) * X a * X b := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [C_mul]; ring
  have e2 : C A.c * (∑ b, C (B.l b) * X b) + (∑ a, C (A.l a) * X a) * C B.c =
      ∑ a, C (A.c * B.l a + B.c * A.l a) * X a := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [C_add, C_mul, C_mul]; ring
  rw [C_mul, ← e1, ← e2]
  ring

end UQ


open MvPolynomial Finset

namespace UQ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def U (x : ι) : Aff ι := ⟨-1, [(x, 2)]⟩
def D (x y : ι) : Aff ι := ⟨-1, [(x, 4), (y, -2)]⟩

def prods (k : ℕ) (s : ℤ) (F H : Aff ι) (v : Fin (k + 2) → ι) : List (Aff ι × Aff ι × ℤ) :=
  (List.finRange (k + 1)).map (fun i => (D (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩),
      D (v ⟨i.val, by omega⟩) (v ⟨i.val + 1, by omega⟩), 3)) ++
    [(U (v ⟨k + 1, by omega⟩), U (v ⟨k + 1, by omega⟩), 9), (F, U (v ⟨0, by omega⟩), -6),
     (H, U (v ⟨k + 1, by omega⟩), 6 * s), (F, F, 1), (H, H, 1)]

noncomputable def prodsMv (L : List (Aff ι × Aff ι × ℤ)) : MvPolynomial ι ℤ :=
  (L.map fun t => C t.2.2 * (t.1.toMv * t.2.1.toMv)).sum

theorem U_toMv (x : ι) : (U x).toMv = 2 * X x - 1 := by
  simp [U, Aff.toMv]; ring

theorem D_toMv (x y : ι) : (D x y).toMv = 2 * (2 * X x - 1) - (2 * X y - 1) := by
  simp [D, Aff.toMv]; ring

theorem chain_eq (k : ℕ) (s : ℤ) (F H : Aff ι) (v : Fin (k + 2) → ι) :
    UnaryQuadraticKKT.Hardness.chainPolynomial k s F.toMv H.toMv (fun j => 2 * X (v j) - 1) =
      prodsMv (prods k s F H v) := by
  unfold UnaryQuadraticKKT.Hardness.chainPolynomial prodsMv prods
  rw [List.map_append, List.sum_append, List.map_map]
  rw [← Fin.sum_univ_def]
  simp only [Function.comp, D_toMv, U_toMv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [Finset.mul_sum]
  have e : ∀ i : Fin (k + 1), C (3 : ℤ) * ((2 * (2 * X (v ⟨i.val, by omega⟩) - 1) - (2 * X (v ⟨i.val + 1, by omega⟩) - 1)) *
      (2 * (2 * X (v ⟨i.val, by omega⟩) - 1) - (2 * X (v ⟨i.val + 1, by omega⟩) - 1))) =
      3 * (2 * (2 * X (v ⟨i.val, by omega⟩) - 1) - (2 * X (v ⟨i.val + 1, by omega⟩) - 1)) ^ 2 := by
    intro i; simp; ring
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [map_neg, map_mul, map_ofNat, C_1]
  ring

end UQ


open MvPolynomial Finset

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

variable {n : ℕ} (p : Quadratic n)

def Fct (a : Option (Fin n)) : Aff (CombinedIndex p) :=
  a.elim ⟨1, []⟩ (fun i => ⟨0, [(.inl i, 1)]⟩)

theorem Fct_toMv (a : Option (Fin n)) : (Fct p a).toMv = factorPolynomial p a := by
  cases a <;> simp [Fct, factorPolynomial, Aff.toMv]

def termProds (r : TermIndex p) : List (Aff (CombinedIndex p) × Aff (CombinedIndex p) × ℤ) :=
  prods (termAt p r).exponent (termAt p r).sign (Fct p (termAt p r).left) (Fct p (termAt p r).right)
    (fun j => .inr ⟨r, j⟩)

def allProds : List (Aff (CombinedIndex p) × Aff (CombinedIndex p) × ℤ) :=
  (List.finRange (dyadicTerms p).length).flatMap (termProds p)

theorem prodsMv_append (L M : List (Aff (CombinedIndex p) × Aff (CombinedIndex p) × ℤ)) :
    prodsMv (L ++ M) = prodsMv L + prodsMv M := by
  simp [prodsMv]

theorem prodsMv_flatMap {β : Type} (l : List β) (f : β → List (Aff (CombinedIndex p) × Aff (CombinedIndex p) × ℤ)) :
    prodsMv (l.flatMap f) = (l.map fun b => prodsMv (f b)).sum := by
  induction l with
  | nil => simp [prodsMv]
  | cons b l ih => simp [List.flatMap_cons, prodsMv_append, ih]

theorem output_eq : outputPolynomial p = prodsMv (allProds p) := by
  unfold outputPolynomial allProds
  rw [prodsMv_flatMap, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold termProds
  rw [← chain_eq, Fct_toMv, Fct_toMv]

end UQ



namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

variable {n : ℕ} (p : Quadratic n)

theorem mem_coord (x : CombinedIndex p) : x ∈ coordinateOrder p := by
  unfold coordinateOrder
  rcases x with i | ⟨r, j⟩
  · simp
  · simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and, List.mem_flatMap]
    right
    exact ⟨r, j, rfl⟩

theorem nodup_coord : (coordinateOrder p).Nodup := by
  unfold coordinateOrder
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange n).map Sum.inl_injective, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun r _ => (List.nodup_finRange _).map (fun a b h => by
        simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact h), ?_⟩
    refine (List.nodup_finRange _).pairwise_of_forall_ne fun r _ r' _ hne => ?_
    simp only [Function.onFun]
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    simp only [List.mem_map, List.mem_finRange, true_and] at ha hb
    obtain ⟨j, rfl⟩ := ha; obtain ⟨j', rfl⟩ := hb
    simp only [Sum.inr.injEq, Sigma.mk.injEq] at hab
    exact hne hab.1
  · intro a ha b hb hab
    simp only [List.mem_map, List.mem_finRange, true_and] at ha
    obtain ⟨i, rfl⟩ := ha
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hb
    obtain ⟨r, j, rfl⟩ := hb
    cases hab

noncomputable def coordEquiv : Fin (outputDimension p) ≃ CombinedIndex p :=
  (nodup_coord p).getEquivOfForallMemList _ (mem_coord p)

theorem coordEquiv_apply (i : Fin (outputDimension p)) : coordEquiv p i = coordinateAt p i := rfl

theorem coordAt_inl (i : ℕ) (hi : i < n) (h : i < outputDimension p) :
    coordinateAt p ⟨i, h⟩ = .inl ⟨i, hi⟩ := by
  unfold coordinateAt
  simp only [Fin.getElem_fin]
  have : ∀ (l : List (CombinedIndex p)) (hl : l = coordinateOrder p) (h' : i < l.length),
      l[i] = .inl ⟨i, hi⟩ := by
    intro l hl h'
    subst hl
    rw [List.getElem_eq_iff]
    unfold coordinateOrder
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hi]
  exact this _ rfl h

end UQ


open Finset

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

theorem integer_out {n : ℕ} (p : Quadratic n) : IntegerCoefficients (outputQuadratic p) := by
  intro t _
  cases t with
  | linear i => simp [coefficient, outputQuadratic]
  | quadratic i j =>
    by_cases h : i = j
    · subst h; simp [coefficient, outputQuadratic]
    · simp [coefficient, outputQuadratic, h]

theorem outDim {n : ℕ} (p : Quadratic n) : outputDimension p = n + auxiliaryCount p := by
  unfold outputDimension coordinateOrder auxiliaryCount
  simp [List.length_flatMap, Fin.sum_univ_def]

theorem slots_le (n : ℕ) : (slots n).length ≤ n * n + n := by
  unfold slots
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_finRange]
  have : ((List.finRange n).map fun i => (((List.finRange n).filter fun j => i ≤ j).map
      (Monomial.quadratic i)).length).sum ≤ ((List.finRange n).map fun _ => n).sum := by
    apply List.sum_le_sum
    intro i _
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  simp at this ⊢
  nlinarith

theorem slots_le_sq (n : ℕ) (hn : 0 < n) : (slots n).length ≤ 2 * n ^ 2 := by
  have := slots_le n
  nlinarith

theorem dyadic_len {n : ℕ} (p : Quadratic n) :
    (dyadicTerms p).length ≤ (slots n).length * normalizationLength p := by
  unfold dyadicTerms
  rw [List.length_flatMap]
  calc ((slots n).map fun t => (((List.finRange (normalizationLength p)).filter
        fun j => coefficientBit p t j).map _).length).sum
      ≤ ((slots n).map fun _ => normalizationLength p).sum := by
        apply List.sum_le_sum
        intro t _
        simp only [List.length_map]
        exact (List.length_filter_le _ _).trans (by simp)
    _ = (slots n).length * normalizationLength p := by simp

theorem exponent_le {n : ℕ} (p : Quadratic n) (r : TermIndex p) :
    (termAt p r).exponent ≤ normalizationLength p := by
  have hmem : termAt p r ∈ dyadicTerms p := List.getElem_mem _
  unfold dyadicTerms at hmem
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hmem
  obtain ⟨t, -, j, -, hj⟩ := hmem
  rw [← hj]
  exact j.isLt

theorem aux_le {n : ℕ} (p : Quadratic n) :
    auxiliaryCount p ≤ (dyadicTerms p).length * (normalizationLength p + 2) := by
  unfold auxiliaryCount
  calc ∑ r : TermIndex p, ((termAt p r).exponent + 2) ≤ ∑ _r : TermIndex p, (normalizationLength p + 2) :=
        Finset.sum_le_sum fun r _ => by have := exponent_le p r; omega
    _ = _ := by simp

end UQ

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

theorem foldl_lcm_dvd (l : List ℕ) : ∀ acc, l.foldl Nat.lcm acc ∣ acc * l.prod := by
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.prod_cons]
    exact (ih _).trans (by rw [← mul_assoc]; exact Nat.mul_dvd_mul_right (Nat.lcm_dvd_mul acc x) _)

theorem dvd_foldl_lcm_acc (l : List ℕ) : ∀ acc, acc ∣ l.foldl Nat.lcm acc := by
  induction l with
  | nil => intro acc; simp
  | cons x xs ih => intro acc; exact (Nat.dvd_lcm_left acc x).trans (ih _)

theorem dvd_foldl_lcm (l : List ℕ) (x : ℕ) (hx : x ∈ l) : ∀ acc, x ∣ l.foldl Nat.lcm acc := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    intro acc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact (Nat.dvd_lcm_right acc x).trans (dvd_foldl_lcm_acc _ _)
    · exact ih h _

theorem foldl_max_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : ∀ acc, acc ≤ B → l.foldl max acc ≤ B := by
  induction l with
  | nil => intro acc h; simpa using h
  | cons x xs ih =>
    intro acc hacc
    exact ih (fun y hy => h y (by simp [hy])) _ (max_le hacc (h x (by simp)))

theorem prod_lt_pow (l : List ℕ) : l.prod ≤ 2 ^ (l.map fun x => x.size).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul (le_of_lt (Nat.lt_size_self x) |>.trans (le_refl _)) ih

theorem norm_len {n : ℕ} (p : Quadratic n) : normalizationLength p ≤ 2 * binaryDataLength p + 1 := by
  set dens := (slots n).map fun t => (coefficient p t).den
  set D := denominatorLCM p
  have hD : D = dens.foldl Nat.lcm 1 := rfl
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso
      have := foldl_lcm_dvd dens 1
      rw [← hD, h, one_mul, zero_dvd_iff] at this
      have : 0 < dens.prod := List.prod_pos (fun x hx => by
        simp only [dens, List.mem_map] at hx; obtain ⟨t, -, rfl⟩ := hx; exact (coefficient p t).den_pos)
      omega
    · exact h
  set Sden := (dens.map fun x => x.size).sum
  have hDle : D ≤ 2 ^ Sden := (Nat.le_of_dvd (List.prod_pos (fun x hx => by
      simp only [dens, List.mem_map] at hx; obtain ⟨t, -, rfl⟩ := hx; exact (coefficient p t).den_pos))
      (by have := foldl_lcm_dvd dens 1; rwa [one_mul] at this)).trans (prod_lt_pow dens)
  set Nb := binaryDataLength p
  have hSden : Sden ≤ Nb := by
    simp only [Sden, dens, Nb, binaryDataLength, List.map_map]
    have : ((slots n).map ((fun x => x.size) ∘ fun t => (coefficient p t).den)).sum ≤
        ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length +
          (coefficient p t).den.bits.length).sum :=
      List.sum_le_sum fun t _ => by simp [Nat.size_eq_bits_len]
    omega
  have hcl : ∀ t ∈ slots n, (clearedCoefficient p t).natAbs < 2 ^ Nb := by
    intro t ht
    set q := coefficient p t
    have hdv : q.den ∣ D := dvd_foldl_lcm dens q.den (List.mem_map.mpr ⟨t, ht, rfl⟩) 1
    obtain ⟨e, he⟩ := hdv
    have hval : (D : ℚ) * q = ((e * q.num : ℤ) : ℚ) := by
      rw [he]; push_cast
      rw [mul_comm (q.den : ℚ) e, mul_assoc, Rat.den_mul_eq_num]
    have hc : clearedCoefficient p t = e * q.num := by
      unfold clearedCoefficient; rw [hval, Rat.num_intCast]
    rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
    have he_le : e ≤ D := by rw [he]; exact Nat.le_mul_of_pos_left e q.den_pos
    have hnum : q.num.natAbs < 2 ^ q.num.natAbs.size := Nat.lt_size_self _
    have hsz : Sden + q.num.natAbs.size ≤ Nb := by
      have h1 : q.num.natAbs.size + q.den.size ≤ 1 + q.num.natAbs.bits.length + q.den.bits.length := by
        simp [Nat.size_eq_bits_len]
      have h2 : 1 + q.num.natAbs.bits.length + q.den.bits.length ≤
          ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length +
            (coefficient p t).den.bits.length).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩)
      have h3 : Sden + q.num.natAbs.size ≤ ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length +
            (coefficient p t).den.bits.length).sum := by
        have e : ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length +
            (coefficient p t).den.bits.length).sum = Sden + ((slots n).map fun t =>
              1 + (coefficient p t).num.natAbs.bits.length).sum := by
          simp only [Sden, dens, List.map_map, Function.comp_def, Nat.size_eq_bits_len]
          rw [← List.sum_map_add]
          congr 1; apply List.map_congr_left; intro t _; ring
        rw [e]
        have : q.num.natAbs.size ≤ ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length).sum :=
          (by simp [Nat.size_eq_bits_len] : q.num.natAbs.size ≤ 1 + q.num.natAbs.bits.length).trans
            (List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩))
        omega
      have : ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length +
            (coefficient p t).den.bits.length).sum ≤ Nb := by simp [Nb, binaryDataLength]
      omega
    calc e * q.num.natAbs ≤ 2 ^ Sden * q.num.natAbs := Nat.mul_le_mul_right _ (he_le.trans hDle)
      _ < 2 ^ Sden * 2 ^ q.num.natAbs.size := by
          rcases Nat.eq_zero_or_pos q.num.natAbs with h0 | h0
          · rw [h0]; simp
          · exact Nat.mul_lt_mul_of_pos_left hnum (by positivity)
      _ = 2 ^ (Sden + q.num.natAbs.size) := by rw [pow_add]
      _ ≤ 2 ^ Nb := Nat.pow_le_pow_right (by norm_num) hsz
  have hM : maximumMagnitude p < 2 ^ (Nb + 1) := by
    unfold maximumMagnitude
    have h1 : 1 ≤ 2 ^ Nb := Nat.one_le_two_pow
    have := foldl_max_le ((slots n).map fun t => (clearedCoefficient p t).natAbs) (2 ^ Nb)
      (fun x hx => by
        simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
        exact (hcl t ht).le) 1 h1
    rw [pow_succ]; omega
  unfold normalizationLength
  rw [Nat.size_eq_bits_len]
  have := Nat.size_le.mpr hM
  omega

end UQ


open MvPolynomial Finset

namespace UQ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def QF.zero : QF ι := ⟨0, fun _ => 0, fun _ _ => 0⟩
def QF.add (F G : QF ι) : QF ι := ⟨F.c + G.c, fun a => F.l a + G.l a, fun a b => F.q a b + G.q a b⟩
def QF.smul (w : ℤ) (F : QF ι) : QF ι := ⟨w * F.c, fun a => w * F.l a, fun a b => w * F.q a b⟩

theorem toMv_zero : (QF.zero : QF ι).toMv = 0 := by simp [QF.zero, QF.toMv]

theorem toMv_add (F G : QF ι) : (F.add G).toMv = F.toMv + G.toMv := by
  show C (F.c + G.c) + ∑ a, C (F.l a + G.l a) * X a + ∑ a, ∑ b, C (F.q a b + G.q a b) * X a * X b =
    (C F.c + ∑ a, C (F.l a) * X a + ∑ a, ∑ b, C (F.q a b) * X a * X b) +
    (C G.c + ∑ a, C (G.l a) * X a + ∑ a, ∑ b, C (G.q a b) * X a * X b)
  have h1 : ∑ a, C (F.l a + G.l a) * X a = ∑ a, C (F.l a) * X a + ∑ a, C (G.l a) * (X a : MvPolynomial ι ℤ) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _ => by rw [C_add, add_mul]
  have h2 : ∑ a, ∑ b, C (F.q a b + G.q a b) * X a * X b =
      ∑ a, ∑ b, C (F.q a b) * X a * X b + ∑ a, ∑ b, C (G.q a b) * X a * (X b : MvPolynomial ι ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by rw [C_add, add_mul, add_mul]
  rw [h1, h2, C_add]
  abel

theorem toMv_smul (w : ℤ) (F : QF ι) : (F.smul w).toMv = C w * F.toMv := by
  show C (w * F.c) + ∑ a, C (w * F.l a) * X a + ∑ a, ∑ b, C (w * F.q a b) * X a * X b =
    C w * (C F.c + ∑ a, C (F.l a) * X a + ∑ a, ∑ b, C (F.q a b) * X a * X b)
  have h1 : ∑ a, C (w * F.l a) * X a = C w * ∑ a, C (F.l a) * (X a : MvPolynomial ι ℤ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by rw [C_mul]; ring
  have h2 : ∑ a, ∑ b, C (w * F.q a b) * X a * X b = C w * ∑ a, ∑ b, C (F.q a b) * X a * (X b : MvPolynomial ι ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by rw [C_mul]; ring
  rw [h1, h2, C_mul]
  ring

def sumQF (L : List (Aff ι × Aff ι × ℤ)) : QF ι :=
  L.foldr (fun t acc => (QF.smul t.2.2 (mulQF t.1 t.2.1)).add acc) QF.zero

theorem prodsMv_eq (L : List (Aff ι × Aff ι × ℤ)) : prodsMv L = (sumQF L).toMv := by
  induction L with
  | nil => simp [prodsMv, sumQF, toMv_zero]
  | cons t L ih =>
    simp only [prodsMv, sumQF, List.map_cons, List.sum_cons, List.foldr_cons] at ih ⊢
    rw [toMv_add, toMv_smul, ← toMv_mul, ← ih]

theorem single_two (a : ι) : (Finsupp.single a 2 : ι →₀ ℕ) = Finsupp.single a 1 + Finsupp.single a 1 := by
  rw [← Finsupp.single_add]

theorem coeff_sq (F : QF ι) (a : ι) : coeff (Finsupp.single a 2) F.toMv = F.q a a := by
  rw [coeff_toMv]
  have h0 : (Finsupp.single a 2 : ι →₀ ℕ) ≠ 0 := by simp
  rw [if_neg h0, zero_add]
  have h1 : ∀ c : ι, (Finsupp.single a 2 : ι →₀ ℕ) ≠ Finsupp.single c 1 := by
    intro c h
    have := congrArg (fun f => f a) h
    by_cases hc : c = a
    · subst hc; simp at this
    · simp [Finsupp.single_apply, hc] at this
  rw [Finset.sum_eq_zero (fun c _ => if_neg (h1 c)), zero_add]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
  · rw [if_pos (single_two a)]
  · intro b _ hb
    rw [if_neg]
    intro h
    have := congrArg (fun f => f b) h
    simp [Finsupp.single_apply, Ne.symm hb] at this
  · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro h
    have := congrArg (fun f => f b) h
    by_cases hcb : c = b
    · subst hcb; simp [Finsupp.single_apply, Ne.symm hb] at this
    · simp [Finsupp.single_apply, Ne.symm hb, Ne.symm hcb] at this
  · simp

end UQ

namespace UQ
open MvPolynomial Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem pair_eq_iff (a b c d : ι) (hab : a ≠ b) :
    (Finsupp.single c 1 + Finsupp.single d 1 : ι →₀ ℕ) = Finsupp.single a 1 + Finsupp.single b 1 ↔
      (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  constructor
  · intro h
    have ha := congrArg (fun f => f a) h
    have hb := congrArg (fun f => f b) h
    simp only [Finsupp.add_apply, Finsupp.single_apply] at ha hb
    rw [if_pos trivial, if_neg (Ne.symm hab)] at ha
    rw [if_pos trivial, if_neg hab] at hb
    split_ifs at ha hb <;> first | omega | (subst_vars; tauto) | tauto
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

theorem single_ne_pair (a b c : ι) : (Finsupp.single c 1 : ι →₀ ℕ) ≠ Finsupp.single a 1 + Finsupp.single b 1 := by
  intro h
  have := congrArg (fun f => f.sum fun _ k => k) h
  simp [Finsupp.sum_add_index] at this

theorem coeff_cross (F : QF ι) (a b : ι) (hab : a ≠ b) :
    coeff (Finsupp.single a 1 + Finsupp.single b 1) F.toMv = F.q a b + F.q b a := by
  rw [coeff_toMv]
  have h0 : (Finsupp.single a 1 + Finsupp.single b 1 : ι →₀ ℕ) ≠ 0 := by
    intro h; have := congrArg (fun f => f a) h; simp at this
  rw [if_neg h0, zero_add, Finset.sum_eq_zero (fun c _ => if_neg (fun h => single_ne_pair a b c h.symm)), zero_add]
  have : ∀ c d : ι, (if (Finsupp.single a 1 + Finsupp.single b 1 : ι →₀ ℕ) = Finsupp.single c 1 + Finsupp.single d 1
      then F.q c d else 0) = (if c = a ∧ d = b then F.q c d else 0) + (if c = b ∧ d = a then F.q c d else 0) := by
    intro c d
    have key : (Finsupp.single a 1 + Finsupp.single b 1 : ι →₀ ℕ) = Finsupp.single c 1 + Finsupp.single d 1 ↔
        (c = a ∧ d = b) ∨ (c = b ∧ d = a) :=
      ⟨fun h => (pair_eq_iff a b c d hab).mp h.symm, fun h => ((pair_eq_iff a b c d hab).mpr h).symm⟩
    simp only [key]
    by_cases h1 : c = a ∧ d = b
    · have h2 : ¬ (c = b ∧ d = a) := fun h2 => hab (h1.1 ▸ h2.1)
      simp [h1, h2]; intro h; exact absurd h hab
    · by_cases h2 : c = b ∧ d = a
      · simp [h1, h2]; intro h; exact absurd h.symm hab
      · simp [h1, h2]
  simp only [this, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b, Finset.sum_eq_single b, Finset.sum_eq_single a]
  · simp [Ne.symm hab]
  all_goals first
    | (intro x _ hx; simp [hx])
    | (intro x _ hx; apply Finset.sum_eq_zero; intro y _; simp [hx])
    | simp

theorem coeff_lin (F : QF ι) (a : ι) : coeff (Finsupp.single a 1) F.toMv = F.l a := by
  rw [coeff_toMv]
  have h0 : (Finsupp.single a 1 : ι →₀ ℕ) ≠ 0 := by simp
  rw [if_neg h0, zero_add]
  rw [Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun d _ => if_neg (single_ne_pair c d a))), add_zero]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; rw [if_neg]; intro h; have := congrArg (fun f => f a) h; simp [Finsupp.single_apply, hb] at this
  · simp

theorem coeff_const (F : QF ι) : coeff 0 F.toMv = F.c := by
  rw [coeff_toMv, if_pos rfl]
  rw [Finset.sum_eq_zero (fun c _ => if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm), add_zero]
  rw [Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun d _ => if_neg (by
    intro h; have := congrArg (fun f => f c) h; simp at this; omega))), add_zero]

end UQ


open MvPolynomial Finset

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

variable {n : ℕ} (p : Quadratic n)

noncomputable def bigQF : QF (CombinedIndex p) := sumQF (allProds p)

theorem out_toMv : outputPolynomial p = (bigQF p).toMv := by rw [output_eq, prodsMv_eq]; rfl

theorem eval_toMv {ι : Type} [Fintype ι] [DecidableEq ι] (F : QF ι) (z : ι → ℝ) :
    eval₂ (Int.castRingHom ℝ) z F.toMv =
      (F.c : ℝ) + ∑ a, (F.l a : ℝ) * z a + ∑ a, ∑ b, (F.q a b : ℝ) * z a * z b := by
  simp [QF.toMv, ← coe_eval₂Hom, map_sum]

theorem eval_chain {ι : Type} [DecidableEq ι] (k : ℕ) (s : ℤ) (f h : MvPolynomial ι ℤ)
    (u : Fin (k + 2) → MvPolynomial ι ℤ) (z : ι → ℝ) :
    eval₂ (Int.castRingHom ℝ) z (chainPolynomial k s f h u) =
      chainValue k s (eval₂ (Int.castRingHom ℝ) z f) (eval₂ (Int.castRingHom ℝ) z h)
        (fun j => eval₂ (Int.castRingHom ℝ) z (u j)) := by
  simp [chainPolynomial, chainValue, ← coe_eval₂Hom, map_sum]

theorem affine_eval (z : CombinedIndex p → ℝ) :
    affineValue p z = eval₂ (Int.castRingHom ℝ) z (outputPolynomial p) := by
  unfold affineValue combinedValue outputPolynomial
  rw [← coe_eval₂Hom, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [coe_eval₂Hom, eval_chain]
  congr 1
  · cases h : (termAt p r).left <;> simp [factorValue, factorPolynomial, affinePoint, h]
  · cases h : (termAt p r).right <;> simp [factorValue, factorPolynomial, affinePoint, h]
  · funext j; simp [affinePoint]

end UQ

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash
variable {n : ℕ} (p : Quadratic n)

theorem coordAt_inj : Function.Injective (coordinateAt p) := (coordEquiv p).injective

theorem outQ_eq (i j : Fin (outputDimension p)) :
    ((outputQuadratic p).Q i j : ℝ) = ((bigQF p).q (coordinateAt p i) (coordinateAt p j) : ℝ) +
      ((bigQF p).q (coordinateAt p j) (coordinateAt p i) : ℝ) := by
  simp only [outputQuadratic]
  split_ifs with h
  · subst h; rw [out_toMv, coeff_sq]; push_cast; ring
  · rw [out_toMv, coeff_cross _ _ _ (fun e => h (coordAt_inj p e))]; push_cast; ring

theorem outc_eq (i : Fin (outputDimension p)) :
    ((outputQuadratic p).c i : ℝ) = ((bigQF p).l (coordinateAt p i) : ℝ) := by
  simp only [outputQuadratic]; rw [out_toMv, coeff_lin]; push_cast; ring

theorem value_identity (z : CombinedIndex p → ℝ) :
    quadraticValue (outputQuadratic p) (fun i => z (coordinateAt p i)) =
      affineValue p z - (outputConstant p : ℝ) := by
  rw [affine_eval, out_toMv, eval_toMv]
  have hc : (outputConstant p : ℝ) = ((bigQF p).c : ℝ) := by
    unfold outputConstant; rw [out_toMv, coeff_const]
  rw [hc]
  unfold quadraticValue
  simp only [outQ_eq, outc_eq]
  set e := coordEquiv p
  have he : ∀ i, coordinateAt p i = e i := fun i => rfl
  simp only [he]
  have h1 : ∑ i, ∑ j, (((bigQF p).q (e i) (e j) : ℝ) + ((bigQF p).q (e j) (e i) : ℝ)) * z (e i) * z (e j) =
      2 * ∑ a, ∑ b, ((bigQF p).q a b : ℝ) * z a * z b := by
    rw [two_mul]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [← e.sum_comp (fun a => ∑ b, ((bigQF p).q a b : ℝ) * z a * z b)]
      exact Finset.sum_congr rfl fun i _ => (e.sum_comp (fun b => ((bigQF p).q (e i) b : ℝ) * z (e i) * z b))
    · rw [Finset.sum_comm, ← e.sum_comp (fun a => ∑ b, ((bigQF p).q a b : ℝ) * z a * z b)]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← e.sum_comp (fun b => ((bigQF p).q (e i) b : ℝ) * z (e i) * z b)]
        exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ((bigQF p).l (e i) : ℝ) * z (e i) = ∑ a, ((bigQF p).l a : ℝ) * z a :=
    e.sum_comp (fun a => ((bigQF p).l a : ℝ) * z a)
  rw [h1, h2]
  ring

end UQ


open MvPolynomial Finset

namespace UQ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def qfMass (F : QF ι) : ℕ := F.c.natAbs + ∑ a, (F.l a).natAbs + ∑ a, ∑ b, (F.q a b).natAbs

def affMass (A : Aff ι) : ℕ := A.c.natAbs + (A.terms.map fun t => t.2.natAbs).sum

theorem sum_l_le (A : Aff ι) : ∑ a, (A.l a).natAbs ≤ (A.terms.map fun t => t.2.natAbs).sum := by
  obtain ⟨c, ts⟩ := A
  induction ts with
  | nil => simp [Aff.l]
  | cons t ts ih =>
    simp only [Aff.l] at ih ⊢
    have hl : ∀ a, ((List.filter (fun t' => decide (t'.1 = a)) (t :: ts)).map Prod.snd).sum =
        (if t.1 = a then t.2 else 0) + ((List.filter (fun t' => decide (t'.1 = a)) ts).map Prod.snd).sum := by
      intro a; by_cases h : t.1 = a <;> simp [List.filter_cons, h]
    simp only [hl, List.map_cons, List.sum_cons]
    calc ∑ a, ((if t.1 = a then t.2 else 0) + ((List.filter (fun t' => decide (t'.1 = a)) ts).map Prod.snd).sum).natAbs
        ≤ ∑ a, ((if t.1 = a then t.2 else 0).natAbs + (((List.filter (fun t' => decide (t'.1 = a)) ts).map Prod.snd).sum).natAbs) :=
          Finset.sum_le_sum fun a _ => Int.natAbs_add_le _ _
      _ = t.2.natAbs + ∑ a, (((List.filter (fun t' => decide (t'.1 = a)) ts).map Prod.snd).sum).natAbs := by
          rw [Finset.sum_add_distrib]; congr 1
          rw [Finset.sum_eq_single t.1]
          · simp
          · intro b _ hb; simp [Ne.symm hb]
          · simp
      _ ≤ _ := by have := ih; omega

theorem qfMass_mul (A B : Aff ι) : qfMass (mulQF A B) ≤ affMass A * affMass B := by
  unfold qfMass mulQF affMass
  simp only
  have hA := sum_l_le A
  have hB := sum_l_le B
  set SA := (A.terms.map fun t => t.2.natAbs).sum
  set SB := (B.terms.map fun t => t.2.natAbs).sum
  have h1 : ∑ a, (A.c * B.l a + B.c * A.l a).natAbs ≤ A.c.natAbs * SB + B.c.natAbs * SA := by
    calc ∑ a, (A.c * B.l a + B.c * A.l a).natAbs ≤ ∑ a, (A.c.natAbs * (B.l a).natAbs + B.c.natAbs * (A.l a).natAbs) :=
          Finset.sum_le_sum fun a _ => by
            have := Int.natAbs_add_le (A.c * B.l a) (B.c * A.l a)
            rw [Int.natAbs_mul, Int.natAbs_mul] at this; exact this
      _ = A.c.natAbs * ∑ a, (B.l a).natAbs + B.c.natAbs * ∑ a, (A.l a).natAbs := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by gcongr
  have h2 : ∑ a, ∑ b, (A.l a * B.l b).natAbs ≤ SA * SB := by
    calc ∑ a, ∑ b, (A.l a * B.l b).natAbs = (∑ a, (A.l a).natAbs) * ∑ b, (B.l b).natAbs := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => Int.natAbs_mul _ _
      _ ≤ SA * SB := Nat.mul_le_mul hA hB
  rw [Int.natAbs_mul]
  nlinarith

theorem qfMass_add (F G : QF ι) : qfMass (F.add G) ≤ qfMass F + qfMass G := by
  unfold qfMass QF.add
  simp only
  have h1 := Int.natAbs_add_le F.c G.c
  have h2 : ∑ a, (F.l a + G.l a).natAbs ≤ ∑ a, (F.l a).natAbs + ∑ a, (G.l a).natAbs := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun a _ => Int.natAbs_add_le _ _
  have h3 : ∑ a, ∑ b, (F.q a b + G.q a b).natAbs ≤ ∑ a, ∑ b, (F.q a b).natAbs + ∑ a, ∑ b, (G.q a b).natAbs := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun b _ => Int.natAbs_add_le _ _
  omega

theorem qfMass_smul (w : ℤ) (F : QF ι) : qfMass (F.smul w) = w.natAbs * qfMass F := by
  unfold qfMass QF.smul
  simp only [Int.natAbs_mul, mul_add, Finset.mul_sum]

theorem qfMass_zero : qfMass (QF.zero : QF ι) = 0 := by simp [qfMass, QF.zero]

theorem qfMass_sumQF (L : List (Aff ι × Aff ι × ℤ)) :
    qfMass (sumQF L) ≤ (L.map fun t => t.2.2.natAbs * (affMass t.1 * affMass t.2.1)).sum := by
  induction L with
  | nil => simp [sumQF, qfMass_zero]
  | cons t L ih =>
    simp only [sumQF, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    refine (qfMass_add _ _).trans ?_
    rw [qfMass_smul]
    have := qfMass_mul t.1 t.2.1
    have h := Nat.mul_le_mul_left t.2.2.natAbs this
    omega

end UQ

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

theorem prods_mass {ι : Type} (k : ℕ) (s : ℤ) (hs : s.natAbs ≤ 1) (F H : Aff ι) (hF : affMass F ≤ 1)
    (hH : affMass H ≤ 1) (v : Fin (k + 2) → ι) :
    ((prods k s F H v).map fun t => t.2.2.natAbs * (affMass t.1 * affMass t.2.1)).sum ≤ 147 * k + 266 := by
  unfold prods
  simp only [List.map_append, List.map_map, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Function.comp_def]
  have hD : ∀ x y : ι, affMass (D x y) = 7 := fun x y => by simp [affMass, D]
  have hU : ∀ x : ι, affMass (U x) = 3 := fun x => by simp [affMass, U]
  simp only [hD, hU]
  have : ((List.finRange (k + 1)).map fun _ => (3 : ℤ).natAbs * (7 * 7)).sum = 147 * (k + 1) := by
    simp; ring
  rw [this]
  have h6 : (6 * s).natAbs ≤ 6 := by rw [Int.natAbs_mul]; simp; omega
  have e1 : (-6 : ℤ).natAbs = 6 := rfl
  have e2 : (9 : ℤ).natAbs = 9 := rfl
  have e3 : (1 : ℤ).natAbs = 1 := rfl
  rw [e1, e2, e3]
  have hFF : affMass F * affMass F ≤ 1 := by nlinarith
  have hHH : affMass H * affMass H ≤ 1 := by nlinarith
  have hHU : (6 * s).natAbs * (affMass H * 3) ≤ 18 := by nlinarith
  nlinarith

variable {n : ℕ} (p : Quadratic n)

theorem Fct_mass (a : Option (Fin n)) : affMass (Fct p a) ≤ 1 := by
  cases a <;> simp [Fct, affMass]

theorem sign_abs (r : TermIndex p) : (termAt p r).sign.natAbs ≤ 1 := by
  have hmem : termAt p r ∈ dyadicTerms p := List.getElem_mem _
  unfold dyadicTerms at hmem
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hmem
  obtain ⟨t, -, j, -, hj⟩ := hmem
  rw [← hj]
  simp only [coefficientSign]; split_ifs <;> simp

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem bigQF_mass : qfMass (bigQF p) ≤ 200 * auxiliaryCount p := by
  refine (qfMass_sumQF _).trans ?_
  unfold allProds auxiliaryCount
  rw [List.map_flatMap, sum_flatMap', Finset.mul_sum, Fin.sum_univ_def]
  apply List.sum_le_sum
  intro r _
  simp only [Function.comp_apply, termProds]
  have := prods_mass (termAt p r).exponent (termAt p r).sign (sign_abs p r) (Fct p (termAt p r).left)
    (Fct p (termAt p r).right) (Fct_mass p _) (Fct_mass p _) (fun j => (Sum.inr ⟨r, j⟩ : CombinedIndex p))
  omega

end UQ


open MvPolynomial Finset

namespace UQ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (e : Fin N ≃ ι)

def pairSet (N : ℕ) : Finset (Fin N × Fin N) := univ.filter fun x => x.1 ≤ x.2

noncomputable def monoSet : Finset (ι →₀ ℕ) :=
  {0} ∪ univ.image (fun a => Finsupp.single a 1) ∪
    (pairSet N).image (fun x => Finsupp.single (e x.1) 1 + Finsupp.single (e x.2) 1)

theorem supp_sub (F : QF ι) : F.toMv.support ⊆ monoSet e := by
  intro m hm
  rw [mem_support_iff, coeff_toMv] at hm
  unfold monoSet
  simp only [mem_union, mem_singleton, mem_image, mem_univ, true_and]
  by_contra hno
  push_neg at hno
  obtain ⟨⟨h0, h1⟩, h2⟩ := hno
  apply hm
  rw [if_neg h0, Finset.sum_eq_zero (fun a _ => if_neg (fun h => h1 a h.symm)), zero_add, zero_add]
  apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _
  rw [if_neg]
  intro h
  by_cases hij : e.symm a ≤ e.symm b
  · exact h2 (e.symm a, e.symm b) (by simp [pairSet, hij]) (by simp [h])
  · exact h2 (e.symm b, e.symm a) (by simp [pairSet]; omega) (by simp [h, add_comm])

theorem pairSet_card (N : ℕ) : 2 * (pairSet N).card = N * N + N := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N × Fin N)))
    (fun x => x.1 ≤ x.2)
  have hlt : (univ.filter fun x : Fin N × Fin N => ¬ x.1 ≤ x.2).card =
      (univ.filter fun x : Fin N × Fin N => x.1 < x.2).card := by
    apply Finset.card_bij (fun x _ => x.swap)
    · intro x hx; simp at hx ⊢; omega
    · intro x _ y _ h; exact Prod.swap_injective h
    · intro y hy; exact ⟨y.swap, by simp at hy ⊢; omega, by simp⟩
  have hle : (pairSet N).card = (univ.filter fun x : Fin N × Fin N => x.1 < x.2).card + N := by
    have h2 := Finset.card_filter_add_card_filter_not (s := pairSet N) (fun x => x.1 < x.2)
    have h3 : ((pairSet N).filter fun x => x.1 < x.2) = univ.filter fun x : Fin N × Fin N => x.1 < x.2 := by
      ext x; simp [pairSet]; omega
    have h4 : ((pairSet N).filter fun x => ¬ x.1 < x.2).card = N := by
      have : ((pairSet N).filter fun x => ¬ x.1 < x.2) = univ.image (fun i : Fin N => (i, i)) := by
        ext x
        simp only [pairSet, mem_filter, mem_univ, true_and, mem_image]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨x.1, Prod.ext rfl (le_antisymm h1 (not_lt.mp h2))⟩
        · rintro ⟨i, rfl⟩; exact ⟨le_rfl, lt_irrefl _⟩
      rw [this, Finset.card_image_of_injective _ (fun i j h => by simpa using h)]; simp
    rw [← h3]; omega
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at hsplit
  unfold pairSet at hle ⊢
  omega

end UQ

namespace UQ
open MvPolynomial Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (e : Fin N ≃ ι)

theorem sum_union_le' {β : Type} [DecidableEq β] (s t : Finset β) (g : β → ℕ) :
    ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  rw [← Finset.sum_union_inter]; omega

theorem card_monoSet : (monoSet e).card ≤ (N + 1) * (N + 2) / 2 := by
  unfold monoSet
  have h1 := Finset.card_union_le ({0} ∪ univ.image (fun a => Finsupp.single a 1))
    ((pairSet N).image (fun x => Finsupp.single (e x.1) 1 + Finsupp.single (e x.2) 1))
  have h2 := Finset.card_union_le ({0} : Finset (ι →₀ ℕ)) (univ.image (fun a => Finsupp.single a 1))
  have h3 := Finset.card_image_le (s := (univ : Finset ι)) (f := fun a => Finsupp.single a 1)
  have h4 := Finset.card_image_le (s := pairSet N) (f := fun x => Finsupp.single (e x.1) 1 + Finsupp.single (e x.2) 1)
  have h5 := pairSet_card N
  have hι : (univ : Finset ι).card = N := by rw [card_univ, ← Fintype.card_fin N]; exact (Fintype.card_congr e).symm
  rw [card_singleton] at h2
  have : (N + 1) * (N + 2) = 2 * (1 + N + (pairSet N).card) := by nlinarith
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

theorem swap_sum (g : Fin N × Fin N → ℕ) :
    ∑ x ∈ pairSet N, (g x + if x.1 < x.2 then g x.swap else 0) = ∑ x, g x := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ x ∈ pairSet N, (if x.1 < x.2 then g x.swap else 0) =
      ∑ x ∈ univ.filter (fun x : Fin N × Fin N => ¬ x.1 ≤ x.2), g x := by
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun x => x.swap) (fun x => x.swap)
    · intro x hx; simp [pairSet] at hx ⊢; omega
    · intro x hx; simp [pairSet] at hx ⊢; omega
    · intro x _; simp
    · intro x _; simp
    · intro x _; rfl
  rw [h1, pairSet, Finset.sum_filter_add_sum_filter_not]

include e in
theorem mass_le (F : QF ι) :
    ∑ m ∈ F.toMv.support, (coeff m F.toMv).natAbs ≤ qfMass F := by
  set g : (ι →₀ ℕ) → ℕ := fun m => (coeff m F.toMv).natAbs
  refine (Finset.sum_le_sum_of_subset_of_nonneg (supp_sub e F) (fun _ _ _ => Nat.zero_le _)).trans ?_
  unfold monoSet
  refine (sum_union_le' _ _ _).trans ?_
  have hA : ∑ m ∈ {0} ∪ univ.image (fun a => Finsupp.single a 1), g m ≤ F.c.natAbs + ∑ a, (F.l a).natAbs := by
    refine (sum_union_le' _ _ _).trans ?_
    rw [Finset.sum_singleton]
    have : g 0 = F.c.natAbs := by simp [g, coeff_const]
    rw [this]
    have := Finset.sum_image_le_of_nonneg (s := (univ : Finset ι)) (g := fun a => Finsupp.single a 1) (f := g)
      (fun _ _ => Nat.zero_le _)
    have e2 : ∑ a, g (Finsupp.single a 1) = ∑ a, (F.l a).natAbs := by simp [g, coeff_lin]
    omega
  have hB : ∑ m ∈ (pairSet N).image (fun x => Finsupp.single (e x.1) 1 + Finsupp.single (e x.2) 1), g m ≤
      ∑ a, ∑ b, (F.q a b).natAbs := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans ?_
    have hx : ∀ x ∈ pairSet N, g (Finsupp.single (e x.1) 1 + Finsupp.single (e x.2) 1) ≤
        (F.q (e x.1) (e x.2)).natAbs + if x.1 < x.2 then (F.q (e x.2) (e x.1)).natAbs else 0 := by
      intro x hx
      simp only [pairSet, mem_filter, mem_univ, true_and] at hx
      by_cases hlt : x.1 < x.2
      · rw [if_pos hlt]
        have hne : e x.1 ≠ e x.2 := fun h => absurd (e.injective h) (ne_of_lt hlt)
        simp only [g]; rw [coeff_cross F _ _ hne]; exact Int.natAbs_add_le _ _
      · rw [if_neg hlt]
        have heq : x.1 = x.2 := le_antisymm hx (not_lt.mp hlt)
        simp only [g]; rw [heq, ← single_two, coeff_sq]; simp
    refine (Finset.sum_le_sum hx).trans ?_
    have hsw := swap_sum (fun x : Fin N × Fin N => (F.q (e x.1) (e x.2)).natAbs)
    simp only [Prod.fst_swap, Prod.snd_swap] at hsw
    rw [hsw]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [← e.sum_comp (fun a => ∑ b, (F.q a b).natAbs)]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => (e.sum_comp (fun b => (F.q (e i) b).natAbs)))
  simp only [g] at hA hB
  unfold qfMass
  omega

end UQ


open MvPolynomial Finset

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

def pairsF (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => ((List.finRange n).filter fun j => decide (i ≤ j)).map fun j => (i, j)

theorem slots_eq (n : ℕ) : slots n =
    (pairsF n).map (fun t => Monomial.quadratic t.1 t.2) ++ (List.finRange n).map Monomial.linear := by
  unfold slots pairsF
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

theorem pairsF_nodup (n : ℕ) : (pairsF n).Nodup := by
  unfold pairsF
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => ((List.nodup_finRange n).filter _).map (fun a b h => by simpa using h), ?_⟩
  refine (List.nodup_finRange n).pairwise_of_forall_ne fun i _ j _ hij => ?_
  simp only [Function.onFun]
  rw [List.disjoint_iff_ne]
  intro a ha b hb h
  simp only [List.mem_map, List.mem_filter] at ha hb
  obtain ⟨x, -, rfl⟩ := ha; obtain ⟨y, -, rfl⟩ := hb
  simp only [Prod.mk.injEq] at h
  exact hij h.1

theorem pairsF_toFinset (n : ℕ) : (pairsF n).toFinset = pairSet n := by
  ext x
  simp only [List.mem_toFinset, pairsF, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq, pairSet, mem_filter, mem_univ]
  constructor
  · rintro ⟨i, j, hij, rfl⟩; exact hij
  · intro h; exact ⟨x.1, x.2, h, rfl⟩

theorem sum_pairsF (n : ℕ) (f : Fin n × Fin n → ℕ) : ((pairsF n).map f).sum = ∑ x ∈ pairSet n, f x := by
  rw [← pairsF_toFinset, List.sum_toFinset _ (pairsF_nodup n)]

theorem len_unaryRat_int (z : ℤ) : (unaryRat (z : ℚ)).length = z.natAbs + 4 := by
  simp [unaryRat, unaryNat]

variable {n : ℕ} (p : Quadratic n)

theorem code_len (hn : 0 < n) : (unaryCode (outputQuadratic p)).length ≤ outputDimension p + 1 +
    200 * auxiliaryCount p + 8 * outputDimension p ^ 2 := by
  set N := outputDimension p
  set e := coordEquiv p
  set F := bigQF p
  have hcoefQ : ∀ i j : Fin N, i ≤ j → ∃ z : ℤ, coefficient (outputQuadratic p) (Monomial.quadratic i j) = z ∧
      z.natAbs ≤ (F.q (e i) (e j)).natAbs + if i < j then (F.q (e j) (e i)).natAbs else 0 := by
    intro i j hij
    by_cases h : i = j
    · subst h
      refine ⟨F.q (e i) (e i), ?_, by simp⟩
      simp only [coefficient, outputQuadratic, if_true]
      rw [out_toMv, coeff_sq]; simp; rfl
    · have hlt : i < j := lt_of_le_of_ne hij h
      refine ⟨F.q (e i) (e j) + F.q (e j) (e i), ?_, by rw [if_pos hlt]; exact Int.natAbs_add_le _ _⟩
      simp only [coefficient, outputQuadratic, h, if_false]
      rw [out_toMv]
      have hc := coeff_cross F (e i) (e j) (fun eq => h (e.injective eq))
      have e1 : coordinateAt p i = e i := rfl
      have e2 : coordinateAt p j = e j := rfl
      rw [e1, e2]
      change ((coeff (Finsupp.single (e i) 1 + Finsupp.single (e j) 1) F.toMv : ℤ) : ℚ) = _
      rw [hc]
  have hcoefL : ∀ i : Fin N, coefficient (outputQuadratic p) (Monomial.linear i) = ((F.l (e i) : ℤ) : ℚ) := by
    intro i; simp only [coefficient, outputQuadratic]; rw [out_toMv, coeff_lin]; rfl
  unfold unaryCode
  rw [List.length_append, List.length_flatMap, slots_eq, List.map_append, List.sum_append, List.map_map,
    List.map_map]
  have hQ : ((pairsF N).map ((fun t => (unaryRat (coefficient (outputQuadratic p) t)).length) ∘
      fun t => Monomial.quadratic t.1 t.2)).sum ≤ ∑ a, ∑ b, (F.q a b).natAbs + 4 * (pairSet N).card := by
    have hpt : ∀ x ∈ pairsF N, ((fun t => (unaryRat (coefficient (outputQuadratic p) t)).length) ∘
        fun t => Monomial.quadratic t.1 t.2) x ≤
        ((F.q (e x.1) (e x.2)).natAbs + if x.1 < x.2 then (F.q (e x.2) (e x.1)).natAbs else 0) + 4 := by
      intro x hx
      have hx' : x.1 ≤ x.2 := by
        have := (List.mem_toFinset.mpr hx); rw [pairsF_toFinset] at this; simpa [pairSet] using this
      obtain ⟨z, hz, hzb⟩ := hcoefQ x.1 x.2 hx'
      simp only [Function.comp_apply, hz, len_unaryRat_int]; omega
    refine (List.sum_le_sum hpt).trans ?_
    rw [sum_pairsF N (fun x => ((F.q (e x.1) (e x.2)).natAbs + if x.1 < x.2 then (F.q (e x.2) (e x.1)).natAbs else 0) + 4)]
    rw [Finset.sum_add_distrib]
    have hsw := swap_sum (fun x : Fin N × Fin N => (F.q (e x.1) (e x.2)).natAbs)
    simp only [Prod.fst_swap, Prod.snd_swap] at hsw
    rw [hsw, ← Finset.univ_product_univ, Finset.sum_product]
    have h1 : ∑ i, ∑ j, (F.q (e i) (e j)).natAbs = ∑ a, ∑ b, (F.q a b).natAbs := by
      rw [← e.sum_comp (fun a => ∑ b, (F.q a b).natAbs)]
      exact Finset.sum_congr rfl fun i _ => e.sum_comp (fun b => (F.q (e i) b).natAbs)
    have h2 : ∑ x ∈ pairSet N, (4 : ℕ) = 4 * (pairSet N).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, h2]
  have hL : ((List.finRange N).map ((fun t => (unaryRat (coefficient (outputQuadratic p) t)).length) ∘
      Monomial.linear)).sum = ∑ a, (F.l a).natAbs + 4 * N := by
    rw [← Fin.sum_univ_def]
    simp only [Function.comp_apply, hcoefL, len_unaryRat_int]
    rw [Finset.sum_add_distrib, e.sum_comp (fun a => (F.l a).natAbs)]
    simp [mul_comm]; rfl
  rw [hL]
  have hm : qfMass F ≤ 200 * auxiliaryCount p := bigQF_mass p
  have hpc := pairSet_card N
  have hN : 1 ≤ N := by show 1 ≤ outputDimension p; rw [outDim]; omega
  have hunary : (unaryNat N).length = N + 1 := by simp [unaryNat]
  unfold qfMass at hm
  have hsq : N ≤ N ^ 2 := by nlinarith
  have key : ∀ (A B C : ℕ), A = N + 1 → B ≤ ∑ a, ∑ b, (F.q a b).natAbs + 4 * (pairSet N).card →
      C = ∑ a, (F.l a).natAbs + 4 * N → A + (B + C) ≤ N + 1 + 200 * auxiliaryCount p + 8 * N ^ 2 := by
    intro A B C hA hB hC
    subst hA hC
    have hpc' : 2 * (pairSet N).card = N ^ 2 + N := by rw [sq]; exact hpc
    have h6 : 6 * N ≤ 6 * N ^ 2 := by linarith
    have hc0 : 0 ≤ F.c.natAbs := Nat.zero_le _
    linarith
  exact key _ _ _ hunary hQ rfl

end UQ


open MvPolynomial Finset

namespace UQ
open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

theorem accounting (n : ℕ) (hn : 0 < n) (p : Quadratic n) :
      normalizationLength p ≤ 2 * binaryDataLength p + 1 ∧
      (dyadicTerms p).length ≤ (slots n).length * normalizationLength p ∧
      (slots n).length ≤ 2 * n ^ 2 ∧
      auxiliaryCount p ≤ (dyadicTerms p).length * (normalizationLength p + 2) ∧
      outputDimension p = n + auxiliaryCount p ∧
      outputCoefficientMass p ≤ 200 * auxiliaryCount p ∧
      (outputPolynomial p).support.card ≤ (outputDimension p + 1) * (outputDimension p + 2) / 2 ∧
      (unaryCode (outputQuadratic p)).length ≤ outputDimension p + 1 +
        200 * auxiliaryCount p + 8 * outputDimension p ^ 2 ∧
      IntegerCoefficients (outputQuadratic p) ∧
      (∀ z : CombinedIndex p → ℝ,
        quadraticValue (outputQuadratic p) (fun i => z (coordinateAt p i)) =
          affineValue p z - (outputConstant p : ℝ)) := by
  refine ⟨norm_len p, dyadic_len p, slots_le_sq n hn, aux_le p, outDim p, ?_, ?_, code_len p hn,
    integer_out p, value_identity p⟩
  · unfold outputCoefficientMass
    rw [out_toMv]
    exact (mass_le (coordEquiv p) _).trans (bigQF_mass p)
  · rw [out_toMv]
    exact (Finset.card_le_card (supp_sub (coordEquiv p) _)).trans (card_monoSet (coordEquiv p))

end UQ

open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash in
theorem solution (n : ℕ) (hn : 0 < n) (p : Quadratic n) :
      normalizationLength p ≤ 2 * binaryDataLength p + 1 ∧
      (dyadicTerms p).length ≤ (slots n).length * normalizationLength p ∧
      (slots n).length ≤ 2 * n ^ 2 ∧
      auxiliaryCount p ≤ (dyadicTerms p).length * (normalizationLength p + 2) ∧
      outputDimension p = n + auxiliaryCount p ∧
      outputCoefficientMass p ≤ 200 * auxiliaryCount p ∧
      (outputPolynomial p).support.card ≤ (outputDimension p + 1) * (outputDimension p + 2) / 2 ∧
      (unaryCode (outputQuadratic p)).length ≤ outputDimension p + 1 +
        200 * auxiliaryCount p + 8 * outputDimension p ^ 2 ∧
      IntegerCoefficients (outputQuadratic p) ∧
      (∀ z : CombinedIndex p → ℝ,
        quadraticValue (outputQuadratic p) (fun i => z (coordinateAt p i)) =
          affineValue p z - (outputConstant p : ℝ)) :=
  UQ.accounting n hn p
