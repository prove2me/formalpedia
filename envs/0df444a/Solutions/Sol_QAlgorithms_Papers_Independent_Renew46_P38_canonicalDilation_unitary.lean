-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.canonicalDilation_unitary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:29:17.226798+00:00
-- url     : https://prove2.me/submissions/1bfcc74e-7a2a-4f3e-bae7-2d64779bd443

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38
noncomputable section

section
variable {A : Type*} [Ring A] [StarRing A] {n : ℕ}

def g64e_W (a : Fin n → A) (g : A) (i j : Fin n) : A :=
  (if i = j then 1 else 0) - a i * g * star (a j)

def g64e_U (a : Fin n → A) (g d : A) : Matrix (Option (Fin n)) (Option (Fin n)) A
  | some i, some j => g64e_W a g i j
  | some i, none => a i
  | none, some j => -star (a j)
  | none, none => d

theorem g64e_sumS (a : Fin n → A) (x y : A) :
    ∑ k, x * star (a k) * (a k * y) = x * (∑ k, star (a k) * a k) * y := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_assoc]

theorem g64e_U_unitary (a : Fin n → A) (g d : A) (hg : star g = g) (hd : star d = d)
    (h1 : (∑ k, star (a k) * a k) + d * d = 1)
    (h2 : (∑ k, star (a k) * a k) * g = 1 - d)
    (h3 : g * (∑ k, star (a k) * a k) = 1 - d)
    (h4 : (1 + d) * g = 1) :
    star (g64e_U a g d) * g64e_U a g d = 1 ∧ g64e_U a g d * star (g64e_U a g d) = 1 := by
  have hWs : ∀ i k, star (g64e_W a g i k) = g64e_W a g k i := by
    intro i k
    unfold g64e_W
    rw [star_sub, star_mul, star_mul, star_star, hg, ← mul_assoc]
    congr 1
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have LW : ∀ i j, (∑ k, g64e_W a g i k * g64e_W a g k j) + a i * star (a j) =
      if i = j then 1 else 0 := by
    intro i j
    have : ∀ k, g64e_W a g i k * g64e_W a g k j =
        ((if i = k then 1 else 0) * (if k = j then 1 else 0)) - (if i = k then a k * g * star (a j) else 0)
        - (if k = j then a i * g * star (a k) else 0) + (a i * g) * star (a k) * (a k * (g * star (a j))) := by
      intro k
      unfold g64e_W
      split_ifs <;> subst_vars <;> noncomm_ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, g64e_sumS, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hgSg : g * (∑ k, star (a k) * a k) * g = g + g - 1 := by
      rw [h3]
      have : d * g = 1 - g := by rw [← h4]; noncomm_ring
      calc (1 - d) * g = g - d * g := by noncomm_ring
        _ = g + g - 1 := by rw [this]; noncomm_ring
    have e : a i * g * (∑ k, star (a k) * a k) * (g * star (a j)) =
        a i * (g * (∑ k, star (a k) * a k) * g) * star (a j) := by noncomm_ring
    rw [e, hgSg]
    split_ifs with h
    · subst h; noncomm_ring
    · noncomm_ring
  have Lw1 : ∀ i, ∑ k, g64e_W a g i k * a k = a i * d := by
    intro i
    simp only [g64e_W, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have : ∑ k, a i * g * star (a k) * a k = a i * g * (∑ k, star (a k) * a k) := by
      rw [Finset.mul_sum]; simp only [mul_assoc]
    rw [this, mul_assoc, h3]; noncomm_ring
  have Lw2 : ∀ j, ∑ k, star (a k) * g64e_W a g k j = d * star (a j) := by
    intro j
    simp only [g64e_W, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have : ∑ k, star (a k) * (a k * g * star (a j)) = (∑ k, star (a k) * a k) * g * star (a j) := by
      rw [Finset.sum_mul, Finset.sum_mul]; simp only [mul_assoc]
    rw [this, h2]; noncomm_ring
  constructor
  · ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.star_apply]
    rcases x with _ | i <;> rcases y with _ | j
    · simp only [g64e_U, hd, Matrix.one_apply_eq]
      rw [add_comm]; exact h1
    · simp only [g64e_U, hd, Matrix.one_apply, reduceCtorEq, if_false]
      rw [Lw2, mul_neg, neg_add_cancel]
    · simp only [g64e_U, hWs, star_neg, star_star, Matrix.one_apply, reduceCtorEq, if_false]
      rw [Lw1, neg_mul, neg_add_cancel]
    · simp only [g64e_U, hWs, star_neg, star_star, neg_mul_neg, Matrix.one_apply, Option.some.injEq]
      rw [add_comm, LW]
  · ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.star_apply]
    rcases x with _ | i <;> rcases y with _ | j
    · simp only [g64e_U, hd, Matrix.one_apply_eq, star_neg, star_star, neg_mul_neg]
      rw [add_comm]; exact h1
    · simp only [g64e_U, hWs, star_neg, star_star, neg_mul, Matrix.one_apply, reduceCtorEq,
        if_false, Finset.sum_neg_distrib]
      rw [Lw2, add_neg_cancel]
    · simp only [g64e_U, hd, star_neg, star_star, mul_neg, Matrix.one_apply, reduceCtorEq,
        if_false, Finset.sum_neg_distrib]
      rw [Lw1, add_neg_cancel]
    · simp only [g64e_U, hWs, Matrix.one_apply, Option.some.injEq]
      rw [add_comm, LW]
end



open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, §3, PDF p. 5, explicit canonical dilation (11)--(12).
Block order is H^n ⊕ H. The first-row a_m* in (12) is corrected to a_n* using
(11) and p=1-aa*. The negative sign in the bottom row is retained. -/
theorem solution (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a = 1) :
    IsStarProjection (columnRangeComplement a) ∧
    IsUnitaryMatrix (columnCanonicalDilation a) ∧
    (∀ i : Fin n, columnCanonicalDilation a (some i) none = a i) ∧
    columnCanonicalDilation a none none = 0 := by
  have hS : (∑ k, star (a k) * a k) = 1 := ha
  have hM : star (Matrix.of (fun i j => a i * star (a j))) = Matrix.of (fun i j => a i * star (a j)) := by
    ext i j; simp [Matrix.star_apply, star_mul]
  have hMM : IsIdempotentElem (Matrix.of (fun i j => a i * star (a j))) := by
    unfold IsIdempotentElem
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have := g64e_sumS a (a i) (star (a j))
    rw [hS, mul_one] at this
    rw [← this]
  have hEq : columnCanonicalDilation a = g64e_U a 1 0 := by
    ext x y
    rcases x with _ | i <;> rcases y with _ | j <;>
      simp [columnCanonicalDilation, g64e_U, g64e_W, columnRangeComplement, Matrix.one_apply]
  have hU := g64e_U_unitary a 1 0 (star_one _) (star_zero _) (by rw [hS]; simp) (by rw [hS]; simp)
    (by rw [hS]; simp) (by simp)
  refine ⟨⟨hMM.one_sub, ?_⟩, ?_, fun i => rfl, rfl⟩
  · show star (1 - Matrix.of (fun i j => a i * star (a j))) = 1 - Matrix.of (fun i j => a i * star (a j))
    rw [star_sub, star_one, hM]
  · rw [hEq]; exact ⟨hU.1, hU.2⟩


end
