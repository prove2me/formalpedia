-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P66.quantumFamily_independent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T03:05:02.524175+00:00
-- url     : https://prove2.me/submissions/c3cf567a-29f3-49b3-858f-27a4b92fb5c7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators
open QAlgorithms (IsDensityMatrix vnEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def AuxSF_G (n : ℕ) (K : Finset (Fin 3)) (j : ℕ) : ℝ :=
  clwTheta n K + (j : ℝ) * clwLambda n K -
    (if 0 ∈ K ∧ 1 ∉ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)^2*((n:ℝ)+1)
     else if 0 ∈ K ∧ 1 ∈ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)*((n:ℝ)+1)^2 else 0)

/-- A uniform bound for |AuxSF_G n K j| when j ≤ n. -/
def AuxWMO_M (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) * (2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ)) +
    2 * (n : ℝ) * ((n : ℝ) + 1)^2

/-- Shift large enough that the ju>0 WMO remainder is controlled by AuxWMO_M. -/
def AuxWMO_k (n : ℕ) : ℝ := 2 * AuxWMO_M n + 1

def AuxH (n : ℕ) (K : Finset (Fin 3)) (j : ℕ) : ℝ :=
  AuxSF_G n K j + AuxWMO_k n * (j : ℝ)

def AuxWitness (n : ℕ) (M : Finset (entropyParty n)) : ℝ :=
  separatingF n M + AuxWMO_k n * (xCount M : ℝ)

theorem AuxWMO_part {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (a : α) :
    (a ∈ A ∧ a ∉ B ∧ a ∉ C) ∨
    (a ∉ A ∧ a ∈ B ∧ a ∉ C) ∨
    (a ∉ A ∧ a ∉ B ∧ a ∈ C) ∨
    (a ∉ A ∧ a ∉ B ∧ a ∉ C) := by
  by_cases hA : a ∈ A
  · exact Or.inl ⟨hA, fun h => Finset.disjoint_left.mp hAB hA h,
      fun h => Finset.disjoint_left.mp hAC hA h⟩
  · by_cases hB : a ∈ B
    · exact Or.inr (Or.inl ⟨hA, hB, fun h => Finset.disjoint_left.mp hBC hB h⟩)
    · by_cases hC : a ∈ C
      · exact Or.inr (Or.inr (Or.inl ⟨hA, hB, hC⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hA, hB, hC⟩))

set_option maxHeartbeats 8000000 in
theorem AuxWMO_P000 (n : ℕ) (hn : 2 ≤ n) (KU KV KW : Finset (Fin 3))
    (ju jv jw : ℕ)
    (hUV : Disjoint KU KV) (hUW : Disjoint KU KW) (hVW : Disjoint KV KW)
    (hs : ju + jv + jw ≤ n)
    (hju : ju = 0)
    (hjv : jv = 0)
    (hjw : jw = 0) :
    AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) ≥
      AuxH n KV jv + AuxH n KW jw := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hn1 : (0:ℝ) ≤ (n:ℝ) + 1 := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((ju + jv + jw : ℕ) : ℝ) := by
    have : ((ju + jv + jw : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hju
  subst hjv
  subst hjw
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := mul_nonneg hs' hn0
  have hh1 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh2 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh3 := mul_nonneg hs' hd
  have hh4 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh5 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh6 := mul_nonneg hs' hn1
  have hh7 := mul_nonneg hd hn0
  have hh8 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh9 := pow_nonneg hn0 2
  have hh10 := pow_nonneg hn0 3
  have hh11 := mul_nonneg hn0 hn1
  have hh12 := pow_nonneg hn1 2
  rcases AuxWMO_part hUV hUW hVW (0 : Fin 3) with
      (⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩) <;>
    rcases AuxWMO_part hUV hUW hVW (1 : Fin 3) with
      (⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩) <;>
    rcases AuxWMO_part hUV hUW hVW (2 : Fin 3) with
      (⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩) <;>
    simp only [AuxH, AuxWMO_k, AuxSF_G, clwTheta, clwLambda,
      u0, v0, w0, u1, v1, w1, u2, v2, w2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 8000000 in
theorem AuxWMO_P001 (n : ℕ) (hn : 2 ≤ n) (KU KV KW : Finset (Fin 3))
    (ju jv jw : ℕ)
    (hUV : Disjoint KU KV) (hUW : Disjoint KU KW) (hVW : Disjoint KV KW)
    (hs : ju + jv + jw ≤ n)
    (hju : ju = 0)
    (hjv : jv = 0)
    (hjw : 0 < jw) :
    AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) ≥
      AuxH n KV jv + AuxH n KW jw := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hn1 : (0:ℝ) ≤ (n:ℝ) + 1 := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((ju + jv + jw : ℕ) : ℝ) := by
    have : ((ju + jv + jw : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hju
  subst hjv
  obtain ⟨jw, rfl⟩ : ∃ m, jw = m + 1 := ⟨jw - 1, by omega⟩
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg jw : (0:ℝ) ≤ jw)
  have hh1 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hd) (pow_nonneg hn0 2)
  have hh7 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hn1
  have hh8 := mul_nonneg hs' hn0
  have hh9 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh10 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh11 := mul_nonneg hs' hd
  have hh12 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh13 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh14 := mul_nonneg hs' hn1
  have hh15 := mul_nonneg hd hn0
  have hh16 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh17 := pow_nonneg hn0 2
  have hh18 := pow_nonneg hn0 3
  have hh19 := mul_nonneg hn0 hn1
  have hh20 := pow_nonneg hn1 2
  rcases AuxWMO_part hUV hUW hVW (0 : Fin 3) with
      (⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩) <;>
    rcases AuxWMO_part hUV hUW hVW (1 : Fin 3) with
      (⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩) <;>
    rcases AuxWMO_part hUV hUW hVW (2 : Fin 3) with
      (⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩) <;>
    simp only [AuxH, AuxWMO_k, AuxSF_G, clwTheta, clwLambda,
      u0, v0, w0, u1, v1, w1, u2, v2, w2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 8000000 in
theorem AuxWMO_P011 (n : ℕ) (hn : 2 ≤ n) (KU KV KW : Finset (Fin 3))
    (ju jv jw : ℕ)
    (hUV : Disjoint KU KV) (hUW : Disjoint KU KW) (hVW : Disjoint KV KW)
    (hs : ju + jv + jw ≤ n)
    (hju : ju = 0)
    (hjv : 0 < jv)
    (hjw : 0 < jw) :
    AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) ≥
      AuxH n KV jv + AuxH n KW jw := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hn1 : (0:ℝ) ≤ (n:ℝ) + 1 := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((ju + jv + jw : ℕ) : ℝ) := by
    have : ((ju + jv + jw : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hju
  obtain ⟨jv, rfl⟩ : ∃ m, jv = m + 1 := ⟨jv - 1, by omega⟩
  obtain ⟨jw, rfl⟩ : ∃ m, jw = m + 1 := ⟨jw - 1, by omega⟩
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg jv : (0:ℝ) ≤ jv)
  have hh1 := mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) hd) (pow_nonneg hn0 2)
  have hh7 := mul_nonneg (Nat.cast_nonneg jv : (0:ℝ) ≤ jv) hn1
  have hh8 := (Nat.cast_nonneg jw : (0:ℝ) ≤ jw)
  have hh9 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hn0
  have hh10 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) (pow_nonneg hn0 2)
  have hh11 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) (pow_nonneg hn0 3)
  have hh12 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hd
  have hh13 := mul_nonneg (mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hd) hn0
  have hh14 := mul_nonneg (mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hd) (pow_nonneg hn0 2)
  have hh15 := mul_nonneg (Nat.cast_nonneg jw : (0:ℝ) ≤ jw) hn1
  have hh16 := mul_nonneg hs' hn0
  have hh17 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh18 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh19 := mul_nonneg hs' hd
  have hh20 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh21 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh22 := mul_nonneg hs' hn1
  have hh23 := mul_nonneg hd hn0
  have hh24 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh25 := pow_nonneg hn0 2
  have hh26 := pow_nonneg hn0 3
  have hh27 := mul_nonneg hn0 hn1
  have hh28 := pow_nonneg hn1 2
  rcases AuxWMO_part hUV hUW hVW (0 : Fin 3) with
      (⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩ | ⟨u0, v0, w0⟩) <;>
    rcases AuxWMO_part hUV hUW hVW (1 : Fin 3) with
      (⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩ | ⟨u1, v1, w1⟩) <;>
    rcases AuxWMO_part hUV hUW hVW (2 : Fin 3) with
      (⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩ | ⟨u2, v2, w2⟩) <;>
    simp only [AuxH, AuxWMO_k, AuxSF_G, clwTheta, clwLambda,
      u0, v0, w0, u1, v1, w1, u2, v2, w2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

theorem AuxWMO_T_nonneg (n : ℕ) :
    0 ≤ 2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]

theorem AuxWMO_theta_inner_nonneg (n : ℕ) (hn : 2 ≤ n) (K : Finset (Fin 3)) :
    0 ≤
      (if 0 ∈ K then
        if 1 ∈ K then 2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1
        else if 2 ∈ K then 2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ) else 2*(n:ℝ)^3 + 5*(n:ℝ)^2
      else if 1 ∈ K then
        if 2 ∈ K then 6*(n:ℝ)^2 + 4*(n:ℝ) - 1 else 4*(n:ℝ)^2 + 2*(n:ℝ) - 1
      else if 2 ∈ K then 3*(n:ℝ)^2 + (n:ℝ) else 0) := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  split_ifs <;> nlinarith [pow_nonneg h0 2, pow_nonneg h0 3]

theorem AuxWMO_theta_inner_le (n : ℕ) (K : Finset (Fin 3)) :
    (if 0 ∈ K then
      if 1 ∈ K then 2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1
      else if 2 ∈ K then 2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ) else 2*(n:ℝ)^3 + 5*(n:ℝ)^2
    else if 1 ∈ K then
      if 2 ∈ K then 6*(n:ℝ)^2 + 4*(n:ℝ) - 1 else 4*(n:ℝ)^2 + 2*(n:ℝ) - 1
    else if 2 ∈ K then 3*(n:ℝ)^2 + (n:ℝ) else 0)
    ≤ 2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ) := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  split_ifs <;> nlinarith [pow_nonneg h0 2, pow_nonneg h0 3]

theorem AuxWMO_theta_abs_le (n : ℕ) (hn : 2 ≤ n) (K : Finset (Fin 3)) :
    |clwTheta n K| ≤ ((n : ℝ) + 1) * (2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ)) := by
  have hnn := AuxWMO_theta_inner_nonneg n hn K
  have hle := AuxWMO_theta_inner_le n K
  have hnp : 0 ≤ (n : ℝ) + 1 := by
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hθ : clwTheta n K =
      ((n : ℝ) + 1) *
        (if 0 ∈ K then
          if 1 ∈ K then 2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1
          else if 2 ∈ K then 2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ) else 2*(n:ℝ)^3 + 5*(n:ℝ)^2
        else if 1 ∈ K then
          if 2 ∈ K then 6*(n:ℝ)^2 + 4*(n:ℝ) - 1 else 4*(n:ℝ)^2 + 2*(n:ℝ) - 1
        else if 2 ∈ K then 3*(n:ℝ)^2 + (n:ℝ) else 0) := by
    simp [clwTheta]
  have hθ0 : 0 ≤ clwTheta n K := by
    rw [hθ]
    exact mul_nonneg hnp hnn
  rw [abs_of_nonneg hθ0, hθ]
  exact mul_le_mul_of_nonneg_left hle hnp

theorem AuxWMO_lambda_inner_nonneg (n : ℕ) (hn : 2 ≤ n) (K : Finset (Fin 3)) :
    0 ≤
      (if 0 ∈ K then
        if 1 ∈ K then 2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1
        else 2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ)
      else if 1 ∈ K then
        if 2 ∈ K then 6*(n:ℝ)^2 + 4*(n:ℝ) - 1 else 4*(n:ℝ)^2 + 2*(n:ℝ) - 1
      else if 2 ∈ K then 4*(n:ℝ)^2 + 2*(n:ℝ) - 1 else (n:ℝ)^2) := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  split_ifs <;> nlinarith [pow_nonneg h0 2, pow_nonneg h0 3]

theorem AuxWMO_lambda_inner_le (n : ℕ) (K : Finset (Fin 3)) :
    (if 0 ∈ K then
      if 1 ∈ K then 2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1
      else 2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ)
    else if 1 ∈ K then
      if 2 ∈ K then 6*(n:ℝ)^2 + 4*(n:ℝ) - 1 else 4*(n:ℝ)^2 + 2*(n:ℝ) - 1
    else if 2 ∈ K then 4*(n:ℝ)^2 + 2*(n:ℝ) - 1 else (n:ℝ)^2)
    ≤ 2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ) := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  split_ifs <;> nlinarith [pow_nonneg h0 2, pow_nonneg h0 3]

theorem AuxWMO_lambda_abs_le (n : ℕ) (hn : 2 ≤ n) (K : Finset (Fin 3)) :
    |clwLambda n K| ≤ 2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ) := by
  have hnn := AuxWMO_lambda_inner_nonneg n hn K
  have hle := AuxWMO_lambda_inner_le n K
  have hLam : clwLambda n K =
      -(if 0 ∈ K then
          if 1 ∈ K then 2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1
          else 2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ)
        else if 1 ∈ K then
          if 2 ∈ K then 6*(n:ℝ)^2 + 4*(n:ℝ) - 1 else 4*(n:ℝ)^2 + 2*(n:ℝ) - 1
        else if 2 ∈ K then 4*(n:ℝ)^2 + 2*(n:ℝ) - 1 else (n:ℝ)^2) := by
    simp [clwLambda]
  have hLe0 : clwLambda n K ≤ 0 := by
    rw [hLam]
    linarith [hnn]
  rw [abs_of_nonpos hLe0, hLam, neg_neg]
  exact hle

theorem AuxWMO_mu_nonneg (n : ℕ) (K : Finset (Fin 3)) (j : ℕ) :
    0 ≤
      (if 0 ∈ K ∧ 1 ∉ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)^2*((n:ℝ)+1)
       else if 0 ∈ K ∧ 1 ∈ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)*((n:ℝ)+1)^2 else 0) := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 ≤ (n : ℝ) + 1 := by linarith
  split_ifs <;> nlinarith [pow_nonneg h0 2, pow_nonneg h1 2]

theorem AuxWMO_mu_le (n : ℕ) (K : Finset (Fin 3)) (j : ℕ) :
    (if 0 ∈ K ∧ 1 ∉ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)^2*((n:ℝ)+1)
     else if 0 ∈ K ∧ 1 ∈ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)*((n:ℝ)+1)^2 else 0)
    ≤ 2 * (n : ℝ) * ((n : ℝ) + 1)^2 := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 ≤ (n : ℝ) + 1 := by linarith
  split_ifs <;> nlinarith [pow_nonneg h0 2, pow_nonneg h1 2]

theorem AuxWMO_G_abs_le (n : ℕ) (hn : 2 ≤ n) (K : Finset (Fin 3)) (j : ℕ)
    (hj : j ≤ n) :
    |AuxSF_G n K j| ≤ AuxWMO_M n := by
  have hTh := AuxWMO_theta_abs_le n hn K
  have hLam := AuxWMO_lambda_abs_le n hn K
  have hMu := AuxWMO_mu_le n K j
  have hMu0 := AuxWMO_mu_nonneg n K j
  have hjn : (j : ℝ) ≤ n := Nat.cast_le.mpr hj
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hT := AuxWMO_T_nonneg n
  let mu : ℝ :=
    (if 0 ∈ K ∧ 1 ∉ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)^2*((n:ℝ)+1)
     else if 0 ∈ K ∧ 1 ∈ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)*((n:ℝ)+1)^2 else 0)
  have hsplit : |AuxSF_G n K j| ≤ |clwTheta n K| + (j : ℝ) * |clwLambda n K| + mu := by
    unfold AuxSF_G
    change |clwTheta n K + (j : ℝ) * clwLambda n K - mu| ≤
      |clwTheta n K| + (j : ℝ) * |clwLambda n K| + mu
    have hjl : |(j : ℝ) * clwLambda n K| = (j : ℝ) * |clwLambda n K| := by
      rw [abs_mul, abs_of_nonneg hj0]
    have hm : |-mu| = mu := by
      rw [abs_neg, abs_of_nonneg hMu0]
    calc
      |clwTheta n K + (j : ℝ) * clwLambda n K - mu|
          = |clwTheta n K + (j : ℝ) * clwLambda n K + (-mu)| := by ring_nf
      _ ≤ |clwTheta n K + (j : ℝ) * clwLambda n K| + |-mu| := abs_add_le _ _
      _ ≤ |clwTheta n K| + |(j : ℝ) * clwLambda n K| + |-mu| := by
          linarith [abs_add_le (clwTheta n K) ((j : ℝ) * clwLambda n K)]
      _ = |clwTheta n K| + (j : ℝ) * |clwLambda n K| + mu := by
          rw [hjl, hm]
  have hsum : |clwTheta n K| + (j : ℝ) * |clwLambda n K| + mu ≤ AuxWMO_M n := by
    have h2 : (j : ℝ) * |clwLambda n K| ≤
        (n : ℝ) * (2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ)) :=
      mul_le_mul hjn hLam (abs_nonneg _) (Nat.cast_nonneg n)
    have hEq : ((n : ℝ) + 1) * (2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ)) +
        (n : ℝ) * (2 * (n : ℝ)^3 + 8 * (n : ℝ)^2 + 4 * (n : ℝ)) +
        2 * (n : ℝ) * ((n : ℝ) + 1)^2 = AuxWMO_M n := by
      simp [AuxWMO_M]; ring
    have hmu : mu ≤ 2 * (n : ℝ) * ((n : ℝ) + 1)^2 := hMu
    linarith [hTh, h2, hmu, hEq]
  exact le_trans hsplit hsum

theorem AuxWMO_M_nonneg (n : ℕ) : 0 ≤ AuxWMO_M n := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 ≤ (n : ℝ) + 1 := by linarith
  have hT := AuxWMO_T_nonneg n
  have h21 : 0 ≤ 2 * (n : ℝ) + 1 := by linarith
  have hL : 0 ≤ 2 * (n : ℝ) * ((n : ℝ) + 1)^2 := by
    nlinarith [pow_nonneg h1 2]
  simp only [AuxWMO_M]
  nlinarith [hT, h21, hL, pow_nonneg h1 2]

theorem AuxWMO_pos (n : ℕ) (hn : 2 ≤ n) (KU KV KW : Finset (Fin 3))
    (ju jv jw : ℕ)
    (hUV : Disjoint KU KV) (hUW : Disjoint KU KW) (hVW : Disjoint KV KW)
    (hs : ju + jv + jw ≤ n) (hju : 0 < ju) :
    AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) ≥
      AuxH n KV jv + AuxH n KW jw := by
  have hj1 : ju + jv ≤ n := by omega
  have hj2 : ju + jw ≤ n := by omega
  have hj3 : jv ≤ n := by omega
  have hj4 : jw ≤ n := by omega
  have a1 := AuxWMO_G_abs_le n hn (KU ∪ KV) (ju + jv) hj1
  have a2 := AuxWMO_G_abs_le n hn (KU ∪ KW) (ju + jw) hj2
  have a3 := AuxWMO_G_abs_le n hn KV jv hj3
  have a4 := AuxWMO_G_abs_le n hn KW jw hj4
  have hG :
      AuxSF_G n (KU ∪ KV) (ju + jv) + AuxSF_G n (KU ∪ KW) (ju + jw) -
        AuxSF_G n KV jv - AuxSF_G n KW jw ≥ -4 * AuxWMO_M n := by
    have ha := add_abs_nonneg (AuxSF_G n (KU ∪ KV) (ju + jv))
    have hb := add_abs_nonneg (AuxSF_G n (KU ∪ KW) (ju + jw))
    have hc := le_abs_self (AuxSF_G n KV jv)
    have hd := le_abs_self (AuxSF_G n KW jw)
    -- ha: 0 ≤ G1 + |G1| so G1 ≥ -|G1|; hc: G3 ≤ |G3| so -G3 ≥ -|G3|
    linarith [ha, hb, hc, hd, a1, a2, a3, a4]
  have hform :
      AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) -
        AuxH n KV jv - AuxH n KW jw =
      (AuxSF_G n (KU ∪ KV) (ju + jv) + AuxSF_G n (KU ∪ KW) (ju + jw) -
        AuxSF_G n KV jv - AuxSF_G n KW jw) +
      AuxWMO_k n * (2 * (ju : ℝ)) := by
    unfold AuxH
    push_cast
    ring
  have hju1 : (1 : ℝ) ≤ ju := by
    exact_mod_cast (Nat.succ_le_of_lt hju)
  have hk : AuxWMO_k n = 2 * AuxWMO_M n + 1 := rfl
  have hM0 := AuxWMO_M_nonneg n
  have : 0 ≤ AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) -
      AuxH n KV jv - AuxH n KW jw := by
    rw [hform, hk]
    nlinarith [hG, hju1, hM0]
  linarith

theorem AuxWMO_key (n : ℕ) (hn : 2 ≤ n) (KU KV KW : Finset (Fin 3))
    (ju jv jw : ℕ)
    (hUV : Disjoint KU KV) (hUW : Disjoint KU KW) (hVW : Disjoint KV KW)
    (hs : ju + jv + jw ≤ n) :
    AuxH n (KU ∪ KV) (ju + jv) + AuxH n (KU ∪ KW) (ju + jw) ≥
      AuxH n KV jv + AuxH n KW jw := by
  have sw : ∀ (A B C : Finset (Fin 3)) (a b c : ℕ),
      Disjoint A B → Disjoint A C → Disjoint B C → a + b + c ≤ n →
      AuxH n (A ∪ C) (a + c) + AuxH n (A ∪ B) (a + b) ≥ AuxH n C c + AuxH n B b →
      AuxH n (A ∪ B) (a + b) + AuxH n (A ∪ C) (a + c) ≥ AuxH n B b + AuxH n C c := by
    intro A B C a b c _ _ _ _ h
    rw [add_comm (AuxH n (A ∪ B) (a + b)), add_comm (AuxH n B b)]
    exact h
  rcases Nat.eq_zero_or_pos ju with hju | hju <;>
    rcases Nat.eq_zero_or_pos jv with hjv | hjv <;>
    rcases Nat.eq_zero_or_pos jw with hjw | hjw
  · exact AuxWMO_P000 n hn KU KV KW ju jv jw hUV hUW hVW hs hju hjv hjw
  · exact AuxWMO_P001 n hn KU KV KW ju jv jw hUV hUW hVW hs hju hjv hjw
  · exact sw KU KV KW ju jv jw hUV hUW hVW (by omega)
      (AuxWMO_P001 n hn KU KW KV ju jw jv hUW hUV hVW.symm (by omega) hju hjw hjv)
  · exact AuxWMO_P011 n hn KU KV KW ju jv jw hUV hUW hVW hs hju hjv hjw
  · exact AuxWMO_pos n hn KU KV KW ju jv jw hUV hUW hVW hs hju
  · exact AuxWMO_pos n hn KU KV KW ju jv jw hUV hUW hVW hs hju
  · exact AuxWMO_pos n hn KU KV KW ju jv jw hUV hUW hVW hs hju
  · exact AuxWMO_pos n hn KU KV KW ju jv jw hUV hUW hVW hs hju

set_option maxHeartbeats 4000000 in
theorem AuxSF_P000 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : w = 0) (hp : p = 0) (hq : q = 0)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hw
  subst hp
  subst hq
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := mul_nonneg hs' hn0
  have hh1 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh2 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh3 := mul_nonneg hs' hd
  have hh4 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh5 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh6 := mul_nonneg hd hn0
  have hh7 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh8 := pow_nonneg hn0 2
  have hh9 := pow_nonneg hn0 3
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp only [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 4000000 in
theorem AuxSF_P001 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : w = 0) (hp : p = 0) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hw
  subst hp
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  have hh1 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2)
  have hh7 := mul_nonneg hs' hn0
  have hh8 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh9 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh10 := mul_nonneg hs' hd
  have hh11 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh12 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh13 := mul_nonneg hd hn0
  have hh14 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh15 := pow_nonneg hn0 2
  have hh16 := pow_nonneg hn0 3
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp only [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 4000000 in
theorem AuxSF_P011 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : w = 0) (hp : 0 < p) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hw
  obtain ⟨p, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg p : (0:ℝ) ≤ p)
  have hh1 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) (pow_nonneg hn0 2)
  have hh7 := (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  have hh8 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0
  have hh9 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2)
  have hh10 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3)
  have hh11 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd
  have hh12 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0
  have hh13 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2)
  have hh14 := mul_nonneg hs' hn0
  have hh15 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh16 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh17 := mul_nonneg hs' hd
  have hh18 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh19 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh20 := mul_nonneg hd hn0
  have hh21 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh22 := pow_nonneg hn0 2
  have hh23 := pow_nonneg hn0 3
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp only [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 4000000 in
theorem AuxSF_P100 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : 0 < w) (hp : p = 0) (hq : q = 0)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  obtain ⟨w, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  subst hp
  subst hq
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg w : (0:ℝ) ≤ w)
  have hh1 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) (pow_nonneg hn0 2)
  have hh7 := mul_nonneg hs' hn0
  have hh8 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh9 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh10 := mul_nonneg hs' hd
  have hh11 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh12 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh13 := mul_nonneg hd hn0
  have hh14 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh15 := pow_nonneg hn0 2
  have hh16 := pow_nonneg hn0 3
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp only [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 4000000 in
theorem AuxSF_P101 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : 0 < w) (hp : p = 0) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  obtain ⟨w, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  subst hp
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg w : (0:ℝ) ≤ w)
  have hh1 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) (pow_nonneg hn0 2)
  have hh7 := (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  have hh8 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0
  have hh9 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2)
  have hh10 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3)
  have hh11 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd
  have hh12 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0
  have hh13 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2)
  have hh14 := mul_nonneg hs' hn0
  have hh15 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh16 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh17 := mul_nonneg hs' hd
  have hh18 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh19 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh20 := mul_nonneg hd hn0
  have hh21 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh22 := pow_nonneg hn0 2
  have hh23 := pow_nonneg hn0 3
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp only [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

set_option maxHeartbeats 4000000 in
theorem AuxSF_P111 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : 0 < w) (hp : 0 < p) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  obtain ⟨w, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  try clear hs
  try clear hn
  try clear hp
  try clear hq
  try clear hw
  try clear hju
  try clear hjv
  try clear hjw
  have hh0 := (Nat.cast_nonneg w : (0:ℝ) ≤ w)
  have hh1 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hn0
  have hh2 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 2)
  have hh3 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 3)
  have hh4 := mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd
  have hh5 := mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) hn0
  have hh6 := mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) (pow_nonneg hn0 2)
  have hh7 := (Nat.cast_nonneg p : (0:ℝ) ≤ p)
  have hh8 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hn0
  have hh9 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 2)
  have hh10 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 3)
  have hh11 := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd
  have hh12 := mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) hn0
  have hh13 := mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) (pow_nonneg hn0 2)
  have hh14 := (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  have hh15 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0
  have hh16 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2)
  have hh17 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3)
  have hh18 := mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd
  have hh19 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0
  have hh20 := mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2)
  have hh21 := mul_nonneg hs' hn0
  have hh22 := mul_nonneg hs' (pow_nonneg hn0 2)
  have hh23 := mul_nonneg hs' (pow_nonneg hn0 3)
  have hh24 := mul_nonneg hs' hd
  have hh25 := mul_nonneg (mul_nonneg hs' hd) hn0
  have hh26 := mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2)
  have hh27 := mul_nonneg hd hn0
  have hh28 := mul_nonneg hd (pow_nonneg hn0 2)
  have hh29 := pow_nonneg hn0 2
  have hh30 := pow_nonneg hn0 3
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp only [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2, Finset.mem_union, Finset.mem_inter, true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add, Nat.add_eq_zero_iff, Nat.add_one_ne_zero, Nat.succ_ne_zero, mul_zero, zero_mul, sub_zero, neg_zero, and_self, or_self] <;>
    linarith

theorem AuxSF_key (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have sw : ∀ (L1 L2 : Finset (Fin 3)) (a b c : ℕ), a + b + c ≤ n →
      AuxSF_G n (L2 ∪ L1) (a + c + b) + AuxSF_G n (L2 ∩ L1) a ≤
        AuxSF_G n L2 (a + c) + AuxSF_G n L1 (a + b) →
      AuxSF_G n (L1 ∪ L2) (a + b + c) + AuxSF_G n (L1 ∩ L2) a ≤
        AuxSF_G n L1 (a + b) + AuxSF_G n L2 (a + c) := by
    intro L1 L2 a b c _ h
    rw [Finset.union_comm, Finset.inter_comm, show a + b + c = a + c + b by ring]; linarith
  rcases Nat.eq_zero_or_pos w with hw | hw <;> rcases Nat.eq_zero_or_pos p with hp | hp <;>
    rcases Nat.eq_zero_or_pos q with hq | hq
  · exact AuxSF_P000 n hn K1 K2 w p q hw hp hq hs
  · exact AuxSF_P001 n hn K1 K2 w p q hw hp hq hs
  · exact sw K1 K2 w p q hs (AuxSF_P001 n hn K2 K1 w q p hw hq hp (by omega))
  · exact AuxSF_P011 n hn K1 K2 w p q hw hp hq hs
  · exact AuxSF_P100 n hn K1 K2 w p q hw hp hq hs
  · exact AuxSF_P101 n hn K1 K2 w p q hw hp hq hs
  · exact sw K1 K2 w p q hs (AuxSF_P101 n hn K2 K1 w q p hw hq hp (by omega))
  · exact AuxSF_P111 n hn K1 K2 w p q hw hp hq hs

theorem AuxSF_spU {n : ℕ} (U V : Finset (entropyParty n)) :
    specialPart (U ∪ V) = specialPart U ∪ specialPart V := by
  ext j; simp [specialPart]

theorem AuxSF_spI {n : ℕ} (U V : Finset (entropyParty n)) :
    specialPart (U ∩ V) = specialPart U ∩ specialPart V := by
  ext j; simp [specialPart]

theorem AuxSF_xc {n : ℕ} (U V : Finset (entropyParty n)) :
    xCount (U ∪ V) + xCount (U ∩ V) = xCount U + xCount V := by
  unfold xCount
  have e1 : (Finset.univ.filter (fun i : Fin n => x i ∈ U ∪ V)) =
      Finset.univ.filter (fun i : Fin n => x i ∈ U) ∪ Finset.univ.filter (fun i : Fin n => x i ∈ V) := by
    ext i; simp
  have e2 : (Finset.univ.filter (fun i : Fin n => x i ∈ U ∩ V)) =
      Finset.univ.filter (fun i : Fin n => x i ∈ U) ∩ Finset.univ.filter (fun i : Fin n => x i ∈ V) := by
    ext i; simp
  rw [e1, e2, Finset.card_union_add_card_inter]

theorem AuxSF_xle {n : ℕ} (U V : Finset (entropyParty n)) (h : U ⊆ V) :
    xCount U ≤ xCount V := by
  unfold xCount
  exact Finset.card_le_card (fun i hi => by simp at hi ⊢; exact h hi)

theorem AuxSF_xn {n : ℕ} (U : Finset (entropyParty n)) : xCount U ≤ n := by
  unfold xCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem AuxSF_sep (n : ℕ) (M : Finset (entropyParty n)) :
    separatingF n M = AuxSF_G n (specialPart M) (xCount M) := by
  have hx : xCount M = 0 ↔ ∀ i : Fin n, Sum.inr i ∉ M := by
    unfold xCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp [x]
  have e1 : M = {entropyLabelA} ↔
      (0 ∈ specialPart M ∧ 1 ∉ specialPart M ∧ 2 ∉ specialPart M ∧ xCount M = 0) := by
    rw [hx]
    simp only [specialPart, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; simp [entropyLabelA]
    · rintro ⟨h0, h1, h2, h3⟩
      ext y
      rcases y with j | i
      · fin_cases j <;> simp_all [entropyLabelA]
      · simp_all [entropyLabelA]
  have e2 : M = {entropyLabelA, b} ↔
      (0 ∈ specialPart M ∧ 1 ∈ specialPart M ∧ 2 ∉ specialPart M ∧ xCount M = 0) := by
    rw [hx]
    simp only [specialPart, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; simp [entropyLabelA, b]
    · rintro ⟨h0, h1, h2, h3⟩
      ext y
      rcases y with j | i
      · fin_cases j <;> simp_all [entropyLabelA, b]
      · simp_all [entropyLabelA, b]
  unfold separatingF AuxSF_G clwMu
  by_cases c1 : M = {entropyLabelA}
  · rw [if_pos c1, if_pos (e1.mp c1)]
  · rw [if_neg c1, if_neg (fun h => c1 (e1.mpr h))]
    by_cases c2 : M = {entropyLabelA, b}
    · rw [if_pos c2, if_pos (e2.mp c2)]
    · rw [if_neg c2, if_neg (fun h => c2 (e2.mpr h))]

section EvLemmas
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem AuxSE_ev_add (L1 L2 : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (L1 + L2) h = evaluateEntropyForm L1 h + evaluateEntropyForm L2 h := by
  simp [evaluateEntropyForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem AuxSE_ev_sub (L1 L2 : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (L1 - L2) h = evaluateEntropyForm L1 h - evaluateEntropyForm L2 h := by
  simp [evaluateEntropyForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem AuxSE_ev_neg (L : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (-L) h = - evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem AuxSE_ev_smul (c : ℝ) (L : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (c • L) h = c * evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem AuxSE_ev_zero (h : Finset P → ℝ) :
    evaluateEntropyForm (0 : Form P) h = 0 := by
  simp [evaluateEntropyForm]

theorem AuxSE_ev_atom (U : Finset P) (h : Finset P → ℝ) :
    evaluateEntropyForm (entropyAtom U) h = if U = ∅ then 0 else h U := by
  unfold evaluateEntropyForm entropyAtom
  split_ifs with hU
  · simp
  · simp [hU, Finset.sum_ite_eq]

theorem AuxSE_ev_atom' (U : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (entropyAtom U) h = h U := by
  rw [AuxSE_ev_atom]
  split_ifs with hU
  · simp [hU, h0]
  · rfl

theorem AuxSE_ev_sum {ι : Type*} [Fintype ι] (f : ι → Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (∑ i, f i) h = ∑ i, evaluateEntropyForm (f i) h := by
  unfold evaluateEntropyForm
  have hfun : ∀ U, (∑ i, f i) U = ∑ i, f i U := by
    intro U
    change ((Finset.univ : Finset ι).sum f) U = Finset.univ.sum (fun i => f i U)
    refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Pi.add_apply, ih]
  calc
    ∑ U, (∑ i, f i) U * h U
        = ∑ U, (∑ i, f i U) * h U := by
          congr 1; ext U; rw [hfun]
    _ = ∑ U, ∑ i, f i U * h U := by
          congr 1; ext U; exact Finset.sum_mul _ _ _
    _ = ∑ i, ∑ U, f i U * h U := Finset.sum_comm
    _ = ∑ i, evaluateEntropyForm (f i) h := by
          simp only [evaluateEntropyForm]

theorem AuxSE_ev_sum_smul {ι : Type*} [Fintype ι] (w : ι → ℝ) (L : ι → Form P)
    (h : Finset P → ℝ) :
    evaluateEntropyForm (∑ i, w i • L i) h =
      ∑ i, w i * evaluateEntropyForm (L i) h := by
  simp [AuxSE_ev_sum, AuxSE_ev_smul]

end EvLemmas

theorem AuxSE_f0 (n : ℕ) : separatingF n (∅ : Finset (entropyParty n)) = 0 := by
  have hAB : (∅ : Finset (entropyParty n)) ≠ {entropyLabelA, b} :=
    Ne.symm (Finset.insert_ne_empty _ _)
  simp [separatingF, clwTheta, clwLambda, specialPart, xCount, clwMu, hAB]

theorem AuxSE_ev_cmi {P : Type*} [Fintype P] [DecidableEq P]
    (U V W : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (cmiForm U V W) h =
      h (U ∪ W) + h (V ∪ W) - h W - h (U ∪ V ∪ W) := by
  unfold cmiForm
  rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0]

theorem AuxSE_ev_mi {P : Type*} [Fintype P] [DecidableEq P]
    (U V : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (miForm U V) h = h U + h V - h (U ∪ V) := by
  unfold miForm
  rw [AuxSE_ev_sub, AuxSE_ev_add,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0]

theorem AuxSE_sp_A {n : ℕ} : specialPart ({entropyLabelA} : Finset (entropyParty n)) = {0} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA]
theorem AuxSE_sp_B {n : ℕ} : specialPart ({b} : Finset (entropyParty n)) = {1} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b]
theorem AuxSE_sp_C {n : ℕ} : specialPart ({c} : Finset (entropyParty n)) = {2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]
theorem AuxSE_sp_AB {n : ℕ} : specialPart ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = {0, 1} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b]
theorem AuxSE_sp_AC {n : ℕ} : specialPart ({entropyLabelA} ∪ {c} : Finset (entropyParty n)) = {0, 2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]
theorem AuxSE_sp_BC {n : ℕ} : specialPart ({b} ∪ {c} : Finset (entropyParty n)) = {1, 2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]
theorem AuxSE_sp_ABC {n : ℕ} :
    specialPart ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = {0, 1, 2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]

theorem AuxSE_xc0_A {n : ℕ} : xCount ({entropyLabelA} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA]
theorem AuxSE_xc0_B {n : ℕ} : xCount ({b} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b]
theorem AuxSE_xc0_C {n : ℕ} : xCount ({c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]
theorem AuxSE_xc0_AB {n : ℕ} : xCount ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b]
theorem AuxSE_xc0_AC {n : ℕ} : xCount ({entropyLabelA} ∪ {c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]
theorem AuxSE_xc0_BC {n : ℕ} : xCount ({b} ∪ {c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]
theorem AuxSE_xc0_ABC {n : ℕ} :
    xCount ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]

theorem AuxSE_G_A0 (n : ℕ) :
    AuxSF_G n {0} 0 = 2 * (n:ℝ)^4 + 5 * (n:ℝ)^3 + 3 * (n:ℝ)^2 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_B0 (n : ℕ) :
    AuxSF_G n {1} 0 = 4 * (n:ℝ)^3 + 6 * (n:ℝ)^2 + (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_C0 (n : ℕ) :
    AuxSF_G n {2} 0 = 3 * (n:ℝ)^3 + 4 * (n:ℝ)^2 + (n:ℝ) := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_AB0 (n : ℕ) :
    AuxSF_G n {0, 1} 0 = 2 * (n:ℝ)^4 + 8 * (n:ℝ)^3 + 8 * (n:ℝ)^2 + (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_AC0 (n : ℕ) :
    AuxSF_G n {0, 2} 0 = 2 * (n:ℝ)^4 + 7 * (n:ℝ)^3 + 7 * (n:ℝ)^2 + 2 * (n:ℝ) := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_BC0 (n : ℕ) :
    AuxSF_G n {1, 2} 0 = 6 * (n:ℝ)^3 + 10 * (n:ℝ)^2 + 3 * (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_ABC0 (n : ℕ) :
    AuxSF_G n {0, 1, 2} 0 = 2 * (n:ℝ)^4 + 10 * (n:ℝ)^3 + 12 * (n:ℝ)^2 + 3 * (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_empty (n j : ℕ) :
    AuxSF_G n ∅ j = - (j : ℝ) * (n:ℝ)^2 := by
  simp [AuxSF_G, clwTheta, clwLambda]

theorem AuxSE_G_A_pos (n j : ℕ) (hj : 0 < j) :
    AuxSF_G n {0} j =
      ((n:ℝ) + 1) * (2*(n:ℝ)^3 + 5*(n:ℝ)^2) + (j:ℝ) * (-(2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ))) := by
  have : ¬ (j = 0) := Nat.pos_iff_ne_zero.mp hj
  simp [AuxSF_G, clwTheta, clwLambda, this]

theorem AuxSE_G_B_pos (n j : ℕ) (hj : 0 < j) :
    AuxSF_G n {1} j =
      ((n:ℝ) + 1) * (4*(n:ℝ)^2 + 2*(n:ℝ) - 1) + (j:ℝ) * (-(4*(n:ℝ)^2 + 2*(n:ℝ) - 1)) := by
  have : ¬ (j = 0) := Nat.pos_iff_ne_zero.mp hj
  simp [AuxSF_G, clwTheta, clwLambda, this]

theorem AuxSE_G_AB_pos (n j : ℕ) (hj : 0 < j) :
    AuxSF_G n {0, 1} j =
      ((n:ℝ) + 1) * (2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1) +
        (j:ℝ) * (-(2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1)) := by
  have : ¬ (j = 0) := Nat.pos_iff_ne_zero.mp hj
  simp [AuxSF_G, clwTheta, clwLambda, this]

theorem AuxSE_f_set {n : ℕ} (M : Finset (entropyParty n)) :
    separatingF n M = AuxSF_G n (specialPart M) (xCount M) := AuxSF_sep n M

theorem AuxSE_I_AC_B (n : ℕ) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (separatingF n) = 0 := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have e1 : specialPart ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = {0, 1} := AuxSE_sp_AB
  have e2 : specialPart ({c} ∪ {b} : Finset (entropyParty n)) = {1, 2} := by
    rw [Finset.union_comm]; exact AuxSE_sp_BC
  have e3 : specialPart ({b} : Finset (entropyParty n)) = {1} := AuxSE_sp_B
  have e4 : specialPart ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) = {0, 1, 2} := by
    have : ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_sp_ABC
  have x1 : xCount ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = 0 := AuxSE_xc0_AB
  have x2 : xCount ({c} ∪ {b} : Finset (entropyParty n)) = 0 := by
    rw [Finset.union_comm]; exact AuxSE_xc0_BC
  have x3 : xCount ({b} : Finset (entropyParty n)) = 0 := AuxSE_xc0_B
  have x4 : xCount ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) = 0 := by
    have : ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_xc0_ABC
  rw [e1, e2, e3, e4, x1, x2, x3, x4, AuxSE_G_AB0, AuxSE_G_BC0, AuxSE_G_B0, AuxSE_G_ABC0]
  ring

theorem AuxSE_I_BC_A (n : ℕ) :
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (separatingF n) = 0 := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have e1 : specialPart ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) = {0, 1} := by
    rw [Finset.union_comm]; exact AuxSE_sp_AB
  have e2 : specialPart ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) = {0, 2} := by
    rw [Finset.union_comm]; exact AuxSE_sp_AC
  have e3 : specialPart ({entropyLabelA} : Finset (entropyParty n)) = {0} := AuxSE_sp_A
  have e4 : specialPart ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) = {0, 1, 2} := by
    have : ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_sp_ABC
  have x1 : xCount ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) = 0 := by
    rw [Finset.union_comm]; exact AuxSE_xc0_AB
  have x2 : xCount ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) = 0 := by
    rw [Finset.union_comm]; exact AuxSE_xc0_AC
  have x3 : xCount ({entropyLabelA} : Finset (entropyParty n)) = 0 := AuxSE_xc0_A
  have x4 : xCount ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) = 0 := by
    have : ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_xc0_ABC
  rw [e1, e2, e3, e4, x1, x2, x3, x4, AuxSE_G_AB0, AuxSE_G_AC0, AuxSE_G_A0, AuxSE_G_ABC0]
  ring

theorem AuxSE_I_AB_C (n : ℕ) :
    evaluateEntropyForm (miForm ({entropyLabelA} ∪ {b}) {c}) (separatingF n) =
      (n:ℝ)^3 - (n:ℝ) := by
  rw [AuxSE_ev_mi _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have e1 : specialPart ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = {0, 1} := AuxSE_sp_AB
  have e2 : specialPart ({c} : Finset (entropyParty n)) = {2} := AuxSE_sp_C
  have e3 : specialPart ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = {0, 1, 2} :=
    AuxSE_sp_ABC
  have x1 : xCount ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = 0 := AuxSE_xc0_AB
  have x2 : xCount ({c} : Finset (entropyParty n)) = 0 := AuxSE_xc0_C
  have x3 : xCount ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = 0 := AuxSE_xc0_ABC
  rw [e1, e2, e3, x1, x2, x3, AuxSE_G_AB0, AuxSE_G_C0, AuxSE_G_ABC0]
  ring


def AuxSE_isX {n : ℕ} (W : Finset (entropyParty n)) : Prop :=
  W ⊆ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t)

theorem AuxSE_eq_of_isX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    W = (Finset.univ.filter (fun i : Fin n => x i ∈ W)).image x := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t) := h hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    obtain ⟨t, rfl⟩ := hy'
    exact Finset.mem_image.mpr ⟨t, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ t, hy⟩, rfl⟩⟩
  · intro hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ht

theorem AuxSE_sp_ofX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart W = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hmem : Sum.inl j ∈ W := (Finset.mem_filter.mp hj).2
  have hx : Sum.inl j ∈ Finset.univ.filter (fun k => ∃ t : Fin n, k = x t) := h hmem
  obtain ⟨_, ⟨t, ht⟩⟩ := Finset.mem_filter.mp hx
  simp only [x] at ht
  exact Sum.inl_ne_inr ht

theorem AuxSE_xc_eq_card {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    xCount W = W.card := by
  let F := Finset.univ.filter (fun i : Fin n => x i ∈ W)
  have hW : W = F.image x := AuxSE_eq_of_isX h
  have hinj : Function.Injective (x : Fin n → entropyParty n) := by
    intro a b hab; simpa [x] using hab
  unfold xCount
  change F.card = W.card
  rw [hW, Finset.card_image_of_injective F hinj]

theorem AuxSE_empty_of_xc0 {n : ℕ} {W : Finset (entropyParty n)}
    (h : AuxSE_isX W) (hx : xCount W = 0) : W = ∅ := by
  rw [← Finset.card_eq_zero, ← AuxSE_xc_eq_card h, hx]

theorem AuxSE_sp_A_unionX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart ({entropyLabelA} ∪ W) = {0} := by
  rw [AuxSF_spU, AuxSE_sp_A, AuxSE_sp_ofX h]; simp

theorem AuxSE_sp_B_unionX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart ({b} ∪ W) = {1} := by
  rw [AuxSF_spU, AuxSE_sp_B, AuxSE_sp_ofX h]; simp

theorem AuxSE_sp_AB_unionX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart (({entropyLabelA} ∪ {b}) ∪ W) = {0, 1} := by
  rw [AuxSF_spU, AuxSE_sp_AB, AuxSE_sp_ofX h]; simp

theorem AuxSE_xc_A_unionX {n : ℕ} {W : Finset (entropyParty n)} :
    xCount ({entropyLabelA} ∪ W) = xCount W := by
  unfold xCount
  refine congr_arg Finset.card ?_
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    cases Finset.mem_union.mp hmem with
    | inl hA =>
      have heq : x i = entropyLabelA := Finset.mem_singleton.mp hA
      simp only [x, entropyLabelA] at heq
      exact (Sum.inr_ne_inl heq).elim
    | inr hW => exact hW
  · intro hi
    obtain ⟨_, hW⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_union.mpr (Or.inr hW)⟩

theorem AuxSE_xc_B_unionX {n : ℕ} {W : Finset (entropyParty n)} :
    xCount ({b} ∪ W) = xCount W := by
  unfold xCount
  refine congr_arg Finset.card ?_
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    cases Finset.mem_union.mp hmem with
    | inl hB =>
      have heq : x i = b := Finset.mem_singleton.mp hB
      simp only [x, b] at heq
      exact (Sum.inr_ne_inl heq).elim
    | inr hW => exact hW
  · intro hi
    obtain ⟨_, hW⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_union.mpr (Or.inr hW)⟩

theorem AuxSE_xc_AB_unionX {n : ℕ} {W : Finset (entropyParty n)} :
    xCount (({entropyLabelA} ∪ {b}) ∪ W) = xCount W := by
  unfold xCount
  refine congr_arg Finset.card ?_
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    cases Finset.mem_union.mp hmem with
    | inl hAB =>
      cases Finset.mem_union.mp hAB with
      | inl hA =>
        have heq : x i = entropyLabelA := Finset.mem_singleton.mp hA
        simp only [x, entropyLabelA] at heq
        exact (Sum.inr_ne_inl heq).elim
      | inr hB =>
        have heq : x i = b := Finset.mem_singleton.mp hB
        simp only [x, b] at heq
        exact (Sum.inr_ne_inl heq).elim
    | inr hW => exact hW
  · intro hi
    obtain ⟨_, hW⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_union.mpr (Or.inr hW)⟩

theorem AuxSE_I_AB_W_empty (n : ℕ) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} (∅ : Finset (entropyParty n))) (separatingF n) =
      (n:ℝ)^3 + (n:ℝ)^2 := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set, Finset.union_empty]
  have e3 : specialPart (∅ : Finset (entropyParty n)) = ∅ := by simp [specialPart]
  have z : xCount (∅ : Finset (entropyParty n)) = 0 := by simp [xCount]
  rw [AuxSE_sp_A, AuxSE_sp_B, e3, AuxSE_sp_AB, AuxSE_xc0_A, AuxSE_xc0_B, z, AuxSE_xc0_AB,
      AuxSE_G_A0, AuxSE_G_B0, AuxSE_G_empty, AuxSE_G_AB0]
  ring

theorem AuxSE_I_AB_W_pos (n : ℕ) {W : Finset (entropyParty n)}
    (hX : AuxSE_isX W) (hj : 0 < xCount W) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} W) (separatingF n) =
      (n:ℝ)^3 - (n:ℝ)^2 - 2 * (n:ℝ) := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have : ({entropyLabelA} ∪ {b} ∪ W : Finset (entropyParty n)) =
      ({entropyLabelA} ∪ {b}) ∪ W := by
    simp [Finset.union_assoc]
  rw [this, AuxSE_sp_A_unionX hX, AuxSE_sp_B_unionX hX, AuxSE_sp_ofX hX, AuxSE_sp_AB_unionX hX,
      AuxSE_xc_A_unionX, AuxSE_xc_B_unionX, AuxSE_xc_AB_unionX,
      AuxSE_G_A_pos n _ hj, AuxSE_G_B_pos n _ hj, AuxSE_G_empty, AuxSE_G_AB_pos n _ hj]
  ring

theorem AuxSE_I_AB_W (n : ℕ) {W : Finset (entropyParty n)} (hX : AuxSE_isX W) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} W) (separatingF n) =
      if xCount W = 0 then (n:ℝ)^3 + (n:ℝ)^2 else (n:ℝ)^3 - (n:ℝ)^2 - 2 * (n:ℝ) := by
  by_cases hj : xCount W = 0
  · have hW : W = ∅ := AuxSE_empty_of_xc0 hX hj
    subst hW
    rw [if_pos hj, AuxSE_I_AB_W_empty]
  · have : 0 < xCount W := Nat.pos_of_ne_zero hj
    rw [if_neg hj, AuxSE_I_AB_W_pos n hX this]


def AuxSE_k {n p : ℕ} (alpha : Fin p → Finset (entropyParty n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card

theorem AuxSE_isX_biUnion {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (h : ∀ i, AuxSE_isX (alpha i)) : AuxSE_isX (Finset.univ.biUnion alpha) := by
  intro y hy
  obtain ⟨i, _, hyi⟩ := Finset.mem_biUnion.mp hy
  exact h i hyi

theorem AuxSE_X_card (n : ℕ) :
    (Finset.univ.filter (fun j : entropyParty n => ∃ t : Fin n, j = x t)).card = n := by
  have h : Finset.univ.filter (fun j : entropyParty n => ∃ t : Fin n, j = x t) =
      (Finset.univ : Finset (Fin n)).image x := by
    ext y
    constructor
    · intro hy
      obtain ⟨_, ⟨t, rfl⟩⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    · intro hy
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, rfl⟩⟩
  rw [h, Finset.card_image_of_injective]
  · simp [Finset.card_univ]
  · intro a b hab; simpa [x] using hab

theorem AuxSE_pairwise {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    (↑(Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint alpha := by
  intro i _ j _ hij
  exact hdisj i j hij

theorem AuxSE_card_biUnion {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    (Finset.univ.biUnion alpha).card = ∑ i, (alpha i).card :=
  Finset.card_biUnion (AuxSE_pairwise hdisj)

theorem AuxSE_xc_biUnion_disjoint {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    xCount (Finset.univ.biUnion alpha) = ∑ i, xCount (alpha i) := by
  rw [AuxSE_xc_eq_card (AuxSE_isX_biUnion hX), AuxSE_card_biUnion hdisj]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact (AuxSE_xc_eq_card (hX i)).symm

theorem AuxSE_k_le_p {n p : ℕ} (alpha : Fin p → Finset (entropyParty n)) :
    AuxSE_k alpha ≤ p := by
  simpa [AuxSE_k, Finset.card_univ] using
    (Finset.card_le_card (Finset.filter_subset (fun i : Fin p => alpha i ≠ ∅) Finset.univ))

theorem AuxSE_k_le_n {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    AuxSE_k alpha ≤ n := by
  have hsum : ∑ i, (alpha i).card = (Finset.univ.biUnion alpha).card :=
    (AuxSE_card_biUnion hdisj).symm
  have hk : AuxSE_k alpha ≤ ∑ i, (alpha i).card := by
    have hrestr :
        ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (alpha i).card =
          ∑ i, (alpha i).card := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have : alpha i = ∅ := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        exact hi
      simp [this]
    rw [← hrestr, AuxSE_k]
    have h1 : ∀ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅),
        1 ≤ (alpha i).card := by
      intro i hi
      have : alpha i ≠ ∅ := (Finset.mem_filter.mp hi).2
      exact Nat.one_le_iff_ne_zero.mpr (mt Finset.card_eq_zero.mp this)
    have : ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (1 : ℕ) =
        (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card := by
      simp [Finset.sum_const]
    calc
      (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card
          = ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (1 : ℕ) := this.symm
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (alpha i).card :=
        Finset.sum_le_sum h1
  have hunion : (Finset.univ.biUnion alpha).card ≤ n := by
    have hle : (Finset.univ.biUnion alpha).card ≤
        (Finset.univ.filter (fun j : entropyParty n => ∃ t : Fin n, j = x t)).card :=
      Finset.card_le_card (AuxSE_isX_biUnion hX)
    rwa [AuxSE_X_card] at hle
  exact hk.trans (hsum.trans_le hunion)

theorem AuxSE_S_ofX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    separatingF n W = - (xCount W : ℝ) * (n : ℝ)^2 := by
  rw [AuxSE_f_set, AuxSE_sp_ofX h, AuxSE_G_empty]

theorem AuxSE_ev_family {n p : ℕ} (alpha : Fin p → Finset (entropyParty n)) :
    evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n) =
      (∑ i, evaluateEntropyForm (cmiForm {entropyLabelA} {b} (alpha i)) (separatingF n)) +
      (∑ i, separatingF n (alpha i)) -
      separatingF n (Finset.univ.biUnion alpha) -
      ((p : ℝ) - 1) *
        evaluateEntropyForm (miForm ({entropyLabelA} ∪ {b}) {c}) (separatingF n) := by
  unfold familyForm
  rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add, AuxSE_ev_sum, AuxSE_ev_sum, AuxSE_ev_smul]
  simp only [AuxSE_ev_atom' _ _ (AuxSE_f0 n)]

theorem AuxSE_sum_I (n : ℕ) {p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i)) :
    ∑ i, evaluateEntropyForm (cmiForm {entropyLabelA} {b} (alpha i)) (separatingF n) =
      ((p - AuxSE_k alpha : ℕ) : ℝ) * ((n : ℝ)^3 + (n : ℝ)^2) +
        (AuxSE_k alpha : ℝ) * ((n : ℝ)^3 - (n : ℝ)^2 - 2 * (n : ℝ)) := by
  have hterm : ∀ i,
      evaluateEntropyForm (cmiForm {entropyLabelA} {b} (alpha i)) (separatingF n) =
        if alpha i = ∅ then (n : ℝ)^3 + (n : ℝ)^2
        else (n : ℝ)^3 - (n : ℝ)^2 - 2 * (n : ℝ) := by
    intro i
    have hiff : xCount (alpha i) = 0 ↔ alpha i = ∅ := by
      constructor
      · exact AuxSE_empty_of_xc0 (hX i)
      · intro h; simp [h, xCount]
    rw [AuxSE_I_AB_W n (hX i)]
    by_cases h0 : xCount (alpha i) = 0
    · rw [if_pos h0, if_pos (hiff.mp h0)]
    · rw [if_neg h0, if_neg (mt hiff.mpr h0)]
  simp_rw [hterm]
  rw [Finset.sum_ite]
  have hempty :
      (Finset.univ.filter (fun i : Fin p => alpha i = ∅)).card = p - AuxSE_k alpha := by
    have hD : Disjoint
        (Finset.univ.filter (fun i : Fin p => alpha i = ∅))
        (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact (Finset.mem_filter.mp hiB).2 (Finset.mem_filter.mp hiA).2
    have hU :
        Finset.univ.filter (fun i : Fin p => alpha i = ∅) ∪
          Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅) = Finset.univ := by
      ext i
      by_cases h : alpha i = ∅ <;> simp [h]
    have hcard := Finset.card_union_of_disjoint hD
    rw [hU, Finset.card_univ, Fintype.card_fin] at hcard
    have hk : (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card = AuxSE_k alpha := rfl
    omega
  have hne :
      (Finset.univ.filter (fun i : Fin p => ¬ alpha i = ∅)).card = AuxSE_k alpha := rfl
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hempty, hne]
  try ring

theorem AuxSE_S_cancel {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    (∑ i, separatingF n (alpha i)) - separatingF n (Finset.univ.biUnion alpha) = 0 := by
  have h1 : ∀ i, separatingF n (alpha i) = - (xCount (alpha i) : ℝ) * (n : ℝ)^2 :=
    fun i => AuxSE_S_ofX (hX i)
  have h2 : separatingF n (Finset.univ.biUnion alpha) =
      - (xCount (Finset.univ.biUnion alpha) : ℝ) * (n : ℝ)^2 :=
    AuxSE_S_ofX (AuxSE_isX_biUnion hX)
  simp_rw [h1, h2, AuxSE_xc_biUnion_disjoint hX hdisj]
  have hsum :
      ∑ x, (-(xCount (alpha x) : ℝ) * (n : ℝ)^2) =
        - (∑ x, (xCount (alpha x) : ℝ)) * (n : ℝ)^2 := by
    simp [mul_comm ((n : ℝ)^2), Finset.sum_mul, Finset.sum_neg_distrib]
  rw [hsum, Nat.cast_sum]
  ring

theorem AuxSE_family_eval {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n) =
      (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + p - 1 - 2 * (AuxSE_k alpha : ℝ)) := by
  rw [AuxSE_ev_family, AuxSE_sum_I n hX, AuxSE_I_AB_C n]
  have hS := AuxSE_S_cancel hX hdisj
  have hpk : ((p - AuxSE_k alpha : ℕ) : ℝ) = (p : ℝ) - (AuxSE_k alpha : ℝ) :=
    Nat.cast_sub (AuxSE_k_le_p alpha)
  rw [hpk]
  linarith

theorem AuxSE_family_nonneg (n p : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p) (hne : p ≠ n)
    {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    0 ≤ evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n) := by
  rw [AuxSE_family_eval hX hdisj]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hk : (0 : ℝ) ≤ (n : ℝ) + p - 1 - 2 * (AuxSE_k alpha : ℝ) := by
    have hk_p := AuxSE_k_le_p (n := n) alpha
    have hk_n := AuxSE_k_le_n hX hdisj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (p : ℝ) + 1 ≤ n := by
        rw [← Nat.cast_succ]
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt hlt)
      have hk_pR : (AuxSE_k alpha : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hk_p
      have : 2 * (AuxSE_k alpha : ℝ) ≤ 2 * (p : ℝ) := by nlinarith [hk_pR]
      nlinarith
    · have : (n : ℝ) + 1 ≤ p := by
        rw [← Nat.cast_succ]
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt hgt)
      have hk_nR : (AuxSE_k alpha : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk_n
      have : 2 * (AuxSE_k alpha : ℝ) ≤ 2 * (n : ℝ) := by nlinarith [hk_nR]
      nlinarith
  exact mul_nonneg (mul_nonneg hn0 hn1) hk

theorem AuxSE_isX_standard {n : ℕ} (i : Fin n) : AuxSE_isX (standardX i) := by
  intro y hy
  have : y = x i := Finset.mem_singleton.mp hy
  subst this
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, rfl⟩⟩

theorem AuxSE_disj_standard {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Disjoint (standardX i) (standardX j) := by
  simp only [standardX, Finset.disjoint_singleton]
  intro h
  have : i = j := by simpa [x] using h
  exact hij this

theorem AuxSE_k_standard (n : ℕ) : AuxSE_k (standardX : Fin n → Finset (entropyParty n)) = n := by
  have h : Finset.univ.filter (fun i : Fin n => standardX i ≠ ∅) = Finset.univ := by
    ext i
    simp [standardX]
  simp [AuxSE_k, h, Finset.card_univ]

theorem AuxSE_standard_eval (n : ℕ) :
    evaluateEntropyForm (standardFamily n) (separatingF n) =
      - (n : ℝ) * ((n : ℝ) + 1) := by
  unfold standardFamily
  have hX : ∀ i : Fin n, AuxSE_isX (standardX i) := AuxSE_isX_standard
  have hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (standardX i) (standardX j) :=
    fun i j hij => AuxSE_disj_standard hij
  rw [AuxSE_family_eval hX hdisj, AuxSE_k_standard]
  ring

theorem separatingF_separates (n : ℕ) (hn : 2 ≤ n) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (separatingF n) = 0 ∧
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (separatingF n) = 0 ∧
    (∀ (p : ℕ), 2 ≤ p → p ≠ n → ∀ alpha : Fin p → Finset (entropyParty n),
      (∀ i, alpha i ⊆ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t)) →
      (∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) →
      0 ≤ evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n)) ∧
    evaluateEntropyForm (standardFamily n) (separatingF n) < 0 := by
  refine ⟨AuxSE_I_AC_B n, AuxSE_I_BC_A n, ?_, ?_⟩
  · intro p hp hpne alpha hXα hdisj
    exact AuxSE_family_nonneg n p hn hp hpne (fun i => hXα i) hdisj
  · rw [AuxSE_standard_eval]
    have hn0 : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn)
    nlinarith


theorem AuxH_sep (n : ℕ) (M : Finset (entropyParty n)) :
    AuxWitness n M = AuxH n (specialPart M) (xCount M) := by
  rw [AuxWitness, AuxH, AuxSF_sep]

theorem AuxWMO_sp_disjoint {n : ℕ} {U V : Finset (entropyParty n)}
    (h : Disjoint U V) : Disjoint (specialPart U) (specialPart V) := by
  refine Finset.disjoint_left.mpr ?_
  intro j hjU hjV
  have hU : Sum.inl j ∈ U := (Finset.mem_filter.mp hjU).2
  have hV : Sum.inl j ∈ V := (Finset.mem_filter.mp hjV).2
  exact Finset.disjoint_left.mp h hU hV

theorem AuxWMO_xc_add {n : ℕ} {U V : Finset (entropyParty n)}
    (h : Disjoint U V) : xCount (U ∪ V) = xCount U + xCount V := by
  have hI : xCount (U ∩ V) = 0 := by
    unfold xCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hx
    have hx' : x i ∈ U ∩ V := hx
    have hUV : x i ∈ U ∧ x i ∈ V := Finset.mem_inter.mp hx'
    exact Finset.disjoint_left.mp h hUV.1 hUV.2
  have := AuxSF_xc U V
  omega

theorem AuxWMO_xc_biUnion {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    xCount (Finset.univ.biUnion alpha) = ∑ i, xCount (alpha i) := by
  let F : Fin p → Finset (Fin n) :=
    fun i => Finset.univ.filter (fun t : Fin n => x t ∈ alpha i)
  have e : Finset.univ.filter (fun t : Fin n => x t ∈ Finset.univ.biUnion alpha) =
      Finset.univ.biUnion F := by
    ext t
    simp [F, Finset.mem_biUnion]
  have hpair : (↑(Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint F := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro t hti htj
    have hi : x t ∈ alpha i := (Finset.mem_filter.mp hti).2
    have hj : x t ∈ alpha j := (Finset.mem_filter.mp htj).2
    exact Finset.disjoint_left.mp (hdisj i j hij) hi hj
  unfold xCount
  rw [e, Finset.card_biUnion hpair]

theorem AuxSF_submodular (n : ℕ) (hn : 2 ≤ n) : IsSubmodular (separatingF n) := by
  intro U V
  rw [AuxSF_sep, AuxSF_sep, AuxSF_sep, AuxSF_sep, AuxSF_spU, AuxSF_spI]
  have h1 := AuxSF_xc U V
  have h2 := AuxSF_xle (U ∩ V) U Finset.inter_subset_left
  have h3 := AuxSF_xle (U ∩ V) V Finset.inter_subset_right
  have h4 := AuxSF_xn (U ∪ V)
  have k := AuxSF_key n hn (specialPart U) (specialPart V) (xCount (U ∩ V))
    (xCount U - xCount (U ∩ V)) (xCount V - xCount (U ∩ V)) (by omega)
  rw [show xCount (U ∩ V) + (xCount U - xCount (U ∩ V)) + (xCount V - xCount (U ∩ V)) =
      xCount (U ∪ V) by omega,
    show xCount (U ∩ V) + (xCount U - xCount (U ∩ V)) = xCount U by omega,
    show xCount (U ∩ V) + (xCount V - xCount (U ∩ V)) = xCount V by omega] at k
  exact k

theorem AuxSE_ev_linear_add {P : Type*} [Fintype P] [DecidableEq P]
    (L : Form P) (h1 h2 : Finset P → ℝ) :
    evaluateEntropyForm L (fun M => h1 M + h2 M) =
      evaluateEntropyForm L h1 + evaluateEntropyForm L h2 := by
  simp [evaluateEntropyForm, mul_add, Finset.sum_add_distrib]

theorem AuxSE_ev_linear_smul {P : Type*} [Fintype P] [DecidableEq P]
    (L : Form P) (c : ℝ) (h : Finset P → ℝ) :
    evaluateEntropyForm L (fun M => c * h M) = c * evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, mul_left_comm, Finset.mul_sum]

theorem AuxWitness_ev {n : ℕ} (L : Form (entropyParty n)) :
    evaluateEntropyForm L (AuxWitness n) =
      evaluateEntropyForm L (separatingF n) +
        AuxWMO_k n * evaluateEntropyForm L (fun M => (xCount M : ℝ)) := by
  change evaluateEntropyForm L (fun M => separatingF n M + AuxWMO_k n * (xCount M : ℝ)) = _
  rw [AuxSE_ev_linear_add L (separatingF n) (fun M => AuxWMO_k n * (xCount M : ℝ)),
      AuxSE_ev_linear_smul]

theorem AuxSE_ev_cmi_xc {n : ℕ} (U V W : Finset (entropyParty n))
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    evaluateEntropyForm (cmiForm U V W) (fun M => (xCount M : ℝ)) = 0 := by
  have h0 : (fun M : Finset (entropyParty n) => (xCount M : ℝ)) ∅ = 0 := by
    simp [xCount]
  rw [AuxSE_ev_cmi U V W (fun M => (xCount M : ℝ)) h0]
  have h1 : xCount (U ∪ W) = xCount U + xCount W := AuxWMO_xc_add hUW
  have h2 : xCount (V ∪ W) = xCount V + xCount W := AuxWMO_xc_add hVW
  have h3 : xCount (U ∪ V ∪ W) = xCount U + xCount V + xCount W := by
    have d : Disjoint (U ∪ V) W := Finset.disjoint_union_left.mpr ⟨hUW, hVW⟩
    have e1 : xCount (U ∪ V) = xCount U + xCount V := AuxWMO_xc_add hUV
    have e2 : xCount ((U ∪ V) ∪ W) = xCount (U ∪ V) + xCount W := AuxWMO_xc_add d
    rw [e1] at e2
    simpa [Finset.union_assoc] using e2
  rw [h1, h2, h3]
  push_cast
  ring

theorem AuxWitness_cmi_eq_f {n : ℕ} {U V W : Finset (entropyParty n)}
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    evaluateEntropyForm (cmiForm U V W) (AuxWitness n) =
      evaluateEntropyForm (cmiForm U V W) (separatingF n) := by
  rw [AuxWitness_ev, AuxSE_ev_cmi_xc U V W hUV hUW hVW, mul_zero, add_zero]

theorem AuxWitness_cmi_nonneg (n : ℕ) (hn : 2 ≤ n)
    {U V W : Finset (entropyParty n)}
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    0 ≤ evaluateEntropyForm (cmiForm U V W) (AuxWitness n) := by
  rw [AuxWitness_cmi_eq_f hUV hUW hVW]
  have h0 : separatingF n (∅ : Finset (entropyParty n)) = 0 := AuxSE_f0 n
  rw [AuxSE_ev_cmi U V W (separatingF n) h0]
  have hsm := AuxSF_submodular n hn (U ∪ W) (V ∪ W)
  have hun : (U ∪ W) ∪ (V ∪ W) = U ∪ V ∪ W := by
    ext y; simp only [Finset.mem_union]; tauto
  have hin : (U ∪ W) ∩ (V ∪ W) = W := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hUoW, hVoW⟩
      rcases hUoW with hU | hW
      · rcases hVoW with hV | hW2
        · exact (Finset.disjoint_left.mp hUV hU hV).elim
        · exact hW2
      · exact hW
    · intro hy
      exact ⟨Or.inr hy, Or.inr hy⟩
  rw [hun, hin] at hsm
  linarith [hsm]

theorem AuxSE_ev_wmo {P : Type*} [Fintype P] [DecidableEq P]
    (U V W : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (wmoForm U V W) h =
      h (U ∪ V) + h (U ∪ W) - h V - h W := by
  unfold wmoForm
  rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add, AuxSE_ev_atom' _ _ h0,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0]

theorem AuxWitness_wmo_nonneg (n : ℕ) (hn : 2 ≤ n)
    {U V W : Finset (entropyParty n)}
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    0 ≤ evaluateEntropyForm (wmoForm U V W) (AuxWitness n) := by
  have h0 : AuxWitness n (∅ : Finset (entropyParty n)) = 0 := by
    have hx : xCount (∅ : Finset (entropyParty n)) = 0 := by simp [xCount]
    rw [AuxWitness, AuxSE_f0, hx]
    simp
  rw [AuxSE_ev_wmo _ _ _ _ h0]
  simp only [AuxH_sep]
  have hspUV : specialPart (U ∪ V) = specialPart U ∪ specialPart V := AuxSF_spU _ _
  have hspUW : specialPart (U ∪ W) = specialPart U ∪ specialPart W := AuxSF_spU _ _
  have hxcUV : xCount (U ∪ V) = xCount U + xCount V := AuxWMO_xc_add hUV
  have hxcUW : xCount (U ∪ W) = xCount U + xCount W := AuxWMO_xc_add hUW
  rw [hspUV, hspUW, hxcUV, hxcUW]
  have hs : xCount U + xCount V + xCount W ≤ n := by
    have : xCount (U ∪ V ∪ W) = xCount U + xCount V + xCount W := by
      have d : Disjoint (U ∪ V) W := Finset.disjoint_union_left.mpr ⟨hUW, hVW⟩
      have e : xCount ((U ∪ V) ∪ W) = xCount (U ∪ V) + xCount W := AuxWMO_xc_add d
      rw [hxcUV] at e
      simpa [Finset.union_assoc] using e
    exact this ▸ AuxSF_xn (U ∪ V ∪ W)
  linarith [AuxWMO_key n hn (specialPart U) (specialPart V) (specialPart W)
    (xCount U) (xCount V) (xCount W)
    (AuxWMO_sp_disjoint hUV) (AuxWMO_sp_disjoint hUW) (AuxWMO_sp_disjoint hVW) hs]

theorem AuxWitness_constr_AC (n : ℕ) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (AuxWitness n) = 0 := by
  have hAC : Disjoint ({entropyLabelA} : Finset (entropyParty n)) {c} := by
    simp [entropyLabelA, c]
  have hAB : Disjoint ({entropyLabelA} : Finset (entropyParty n)) {b} := by
    simp [entropyLabelA, b]
  have hCB : Disjoint ({c} : Finset (entropyParty n)) {b} := by
    simp [b, c]
  rw [AuxWitness_cmi_eq_f (U := {entropyLabelA}) (V := {c}) (W := {b}) hAC hAB hCB]
  exact AuxSE_I_AC_B n

theorem AuxWitness_constr_BC (n : ℕ) :
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (AuxWitness n) = 0 := by
  have hBC : Disjoint ({b} : Finset (entropyParty n)) {c} := by
    simp [b, c]
  have hBA : Disjoint ({b} : Finset (entropyParty n)) {entropyLabelA} := by
    simp [entropyLabelA, b]
  have hCA : Disjoint ({c} : Finset (entropyParty n)) {entropyLabelA} := by
    simp [entropyLabelA, c]
  rw [AuxWitness_cmi_eq_f (U := {b}) (V := {c}) (W := {entropyLabelA}) hBC hBA hCA]
  exact AuxSE_I_BC_A n

theorem AuxSE_ev_mi_xc {n : ℕ} (U V : Finset (entropyParty n)) (hUV : Disjoint U V) :
    evaluateEntropyForm (miForm U V) (fun M => (xCount M : ℝ)) = 0 := by
  have h0 : (fun M : Finset (entropyParty n) => (xCount M : ℝ)) ∅ = 0 := by
    simp [xCount]
  rw [AuxSE_ev_mi U V (fun M => (xCount M : ℝ)) h0]
  have h : xCount (U ∪ V) = xCount U + xCount V := AuxWMO_xc_add hUV
  rw [h]
  push_cast
  ring

theorem AuxSE_ev_atom_xc {n : ℕ} (U : Finset (entropyParty n)) :
    evaluateEntropyForm (entropyAtom U) (fun M => (xCount M : ℝ)) = (xCount U : ℝ) := by
  have h0 : (fun M : Finset (entropyParty n) => (xCount M : ℝ)) ∅ = 0 := by
    simp [xCount]
  exact AuxSE_ev_atom' U (fun M => (xCount M : ℝ)) h0

theorem AuxInst_disjUV {n p : ℕ} {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (h : DisjointInstance U V W alpha) : Disjoint U V := h.1.1

theorem AuxInst_disjUW {n p : ℕ} {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (h : DisjointInstance U V W alpha) : Disjoint U W := h.1.2.1

theorem AuxInst_disjVW {n p : ℕ} {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (h : DisjointInstance U V W alpha) : Disjoint V W := h.1.2.2

theorem AuxInst_disj_alpha {n p : ℕ} {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (h : DisjointInstance U V W alpha) (i : Fin p) :
    Disjoint U (alpha i) ∧ Disjoint V (alpha i) ∧ Disjoint (alpha i) W := by
  have hα : Disjoint (alpha i) (U ∪ V ∪ W) := h.2.1 i
  have h1 : Disjoint ((U ∪ V) ∪ W) (alpha i) := by
    simpa [Finset.union_assoc] using hα.symm
  have h2 := Finset.disjoint_union_left.mp h1
  have h3 := Finset.disjoint_union_left.mp h2.1
  exact ⟨h3.1, h3.2, h2.2.symm⟩

theorem AuxWitness_family_xc {n p : ℕ} (U V W : Finset (entropyParty n))
    (alpha : Fin p → Finset (entropyParty n))
    (hInst : DisjointInstance U V W alpha) :
    evaluateEntropyForm (familyForm U V W alpha)
      (fun M => (xCount M : ℝ)) = 0 := by
  have hUV := AuxInst_disjUV hInst
  have hUW := AuxInst_disjUW hInst
  have hVW := AuxInst_disjVW hInst
  have hαdis : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j) := hInst.2.2
  unfold familyForm
  rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add, AuxSE_ev_sum, AuxSE_ev_sum, AuxSE_ev_smul]
  have hI : ∀ i, evaluateEntropyForm (cmiForm U V (alpha i))
      (fun M => (xCount M : ℝ)) = 0 := by
    intro i
    have hi := AuxInst_disj_alpha hInst i
    exact AuxSE_ev_cmi_xc U V (alpha i) hUV hi.1 hi.2.1
  have hS : ∀ i, evaluateEntropyForm (entropyAtom (alpha i))
      (fun M => (xCount M : ℝ)) = (xCount (alpha i) : ℝ) :=
    fun i => AuxSE_ev_atom_xc (alpha i)
  have hUn : evaluateEntropyForm (entropyAtom (Finset.univ.biUnion alpha))
      (fun M => (xCount M : ℝ)) = (xCount (Finset.univ.biUnion alpha) : ℝ) :=
    AuxSE_ev_atom_xc _
  have hMI : evaluateEntropyForm (miForm (U ∪ V) W)
      (fun M => (xCount M : ℝ)) = 0 := by
    have d : Disjoint (U ∪ V) W := Finset.disjoint_union_left.mpr ⟨hUW, hVW⟩
    exact AuxSE_ev_mi_xc (U ∪ V) W d
  simp only [hI, hS, hUn, hMI, Finset.sum_const_zero, smul_eq_mul, mul_zero]
  have hsum : (xCount (Finset.univ.biUnion alpha) : ℝ) = ∑ i, (xCount (alpha i) : ℝ) := by
    exact_mod_cast (AuxWMO_xc_biUnion hαdis)
  simp [hsum]

theorem AuxWitness_family_eq_f {n p : ℕ} {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (hInst : DisjointInstance U V W alpha) :
    evaluateEntropyForm (familyForm U V W alpha) (AuxWitness n) =
      evaluateEntropyForm (familyForm U V W alpha) (separatingF n) := by
  rw [AuxWitness_ev, AuxWitness_family_xc U V W alpha hInst, mul_zero, add_zero]

theorem AuxWitness_subadd {n : ℕ} (hn : 2 ≤ n) {U V : Finset (entropyParty n)}
    (hUV : Disjoint U V) :
    AuxWitness n (U ∪ V) ≤ AuxWitness n U + AuxWitness n V := by
  have h0 : separatingF n (∅ : Finset (entropyParty n)) = 0 := AuxSE_f0 n
  have hsm := AuxSF_submodular n hn U V
  have hI : U ∩ V = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hUV
  rw [hI] at hsm
  have hxc : xCount (U ∪ V) = xCount U + xCount V := AuxWMO_xc_add hUV
  unfold AuxWitness
  rw [hxc]
  push_cast
  linarith [hsm, h0]

theorem AuxWitness_sum_alpha {n p : ℕ} (hn : 2 ≤ n)
    {alpha : Fin p → Finset (entropyParty n)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    AuxWitness n (Finset.univ.biUnion alpha) ≤ ∑ i, AuxWitness n (alpha i) := by
  classical
  have hgen : ∀ s : Finset (Fin p),
      AuxWitness n (s.biUnion alpha) ≤ ∑ i ∈ s, AuxWitness n (alpha i) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have hx : xCount (∅ : Finset (entropyParty n)) = 0 := by simp [xCount]
        have : (∅ : Finset (Fin p)).biUnion alpha = ∅ := by simp
        rw [this, AuxWitness, AuxSE_f0, hx]
        simp
    | insert i s hi hs =>
        have hdis : Disjoint (alpha i) (s.biUnion alpha) := by
          refine Finset.disjoint_left.mpr ?_
          intro y hyi hys
          obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hys
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          exact Finset.disjoint_left.mp (hdisj i j hij) hyi hyj
        have : (insert i s).biUnion alpha = alpha i ∪ s.biUnion alpha :=
          Finset.biUnion_insert
        rw [this, Finset.sum_insert hi]
        linarith [AuxWitness_subadd (n := n) (hn := hn) (U := alpha i) (V := s.biUnion alpha) hdis]
  exact hgen Finset.univ

theorem AuxForm_cmi_zero_emptyU {P : Type*} [DecidableEq P] (V W : Finset P) :
    cmiForm (∅ : Finset P) V W = 0 := by
  ext S
  unfold cmiForm entropyAtom
  simp

theorem AuxForm_cmi_zero_emptyV {P : Type*} [DecidableEq P] (U W : Finset P) :
    cmiForm U (∅ : Finset P) W = 0 := by
  ext S
  unfold cmiForm entropyAtom
  simp [Finset.union_comm]

theorem AuxForm_atom_apply {P : Type*} [DecidableEq P] (U S : Finset P) :
    entropyAtom U S = if U = ∅ then (0 : ℝ) else if S = U then 1 else 0 := by
  unfold entropyAtom
  by_cases hU : U = ∅
  · simp [hU]
  · simp [hU]

theorem AuxForm_cmi_eq_zero_of_triple {P : Type*} [Fintype P] [DecidableEq P]
    {U V W : Finset P} (h : DisjointTriple U V W) :
    cmiForm U V W = 0 ↔ U = ∅ ∨ V = ∅ := by
  constructor
  · intro hf
    by_contra hne
    have hUne : U ≠ ∅ := fun hU => hne (Or.inl hU)
    have hVne : V ≠ ∅ := fun hV => hne (Or.inr hV)
    have hUV : Disjoint U V := h.1
    have hUW : Disjoint U W := h.2.1
    have hVW : Disjoint V W := h.2.2
    have hSne : U ∪ W ≠ ∅ := by
      intro hE; exact hUne (Finset.union_eq_empty.mp hE).1
    have hcoef : cmiForm U V W (U ∪ W) = 1 := by
      unfold cmiForm
      have a1 : entropyAtom (U ∪ W) (U ∪ W) = 1 := by
        rw [AuxForm_atom_apply, if_neg hSne, if_pos rfl]
      have a2 : entropyAtom (V ∪ W) (U ∪ W) = 0 := by
        rw [AuxForm_atom_apply]
        split_ifs with h0 heq
        · rfl
        · have hUsub : U ⊆ V ∪ W := by
            intro x hx; rw [← heq]; exact Finset.mem_union.mpr (Or.inl hx)
          have hUemp : U = ∅ := by
            ext x
            constructor
            · intro hx
              have hx' := hUsub hx
              rcases Finset.mem_union.mp hx' with hxV | hxW
              · exact (Finset.disjoint_left.mp hUV hx hxV).elim
              · exact (Finset.disjoint_left.mp hUW hx hxW).elim
            · intro hx; exact (Finset.notMem_empty x hx).elim
          exact (hUne hUemp).elim
        · rfl
      have a3 : entropyAtom W (U ∪ W) = 0 := by
        rw [AuxForm_atom_apply]
        split_ifs with h0 heq
        · rfl
        · have hUsub : U ⊆ W := by
            intro x hx
            have : x ∈ U ∪ W := Finset.mem_union.mpr (Or.inl hx)
            simpa [heq] using this
          have hUemp : U = ∅ := by
            ext x
            constructor
            · intro hx; exact (Finset.disjoint_left.mp hUW hx (hUsub hx)).elim
            · intro hx; exact (Finset.notMem_empty x hx).elim
          exact (hUne hUemp).elim
        · rfl
      have a4 : entropyAtom (U ∪ (V ∪ W)) (U ∪ W) = 0 := by
        rw [AuxForm_atom_apply]
        split_ifs with h0 heq
        · rfl
        · have hVsub : V ⊆ U ∪ W := by
            intro x hx
            have : x ∈ U ∪ (V ∪ W) := by simp [hx]
            simpa [heq] using this
          have hVemp : V = ∅ := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_union.mp (hVsub hx) with hxU | hxW
              · exact (Finset.disjoint_left.mp hUV hxU hx).elim
              · exact (Finset.disjoint_left.mp hVW hx hxW).elim
            · intro hx; exact (Finset.notMem_empty x hx).elim
          exact (hVne hVemp).elim
        · rfl
      simp [a1, a2, a3, a4]
    have hcoef' : (0 : ℝ) = 1 := by
      have hfun : (0 : Form P) (U ∪ W) = 0 := by simp
      rw [hf] at hcoef
      exact hfun.symm.trans hcoef
    exact zero_ne_one hcoef'
  · rintro (hU | hV)
    · subst hU; exact AuxForm_cmi_zero_emptyU V W
    · subst hV; exact AuxForm_cmi_zero_emptyV U W

theorem AuxForm_labels_ne {n : ℕ} :
    (entropyLabelA : entropyParty n) ≠ b ∧
    (entropyLabelA : entropyParty n) ≠ c ∧
    (b : entropyParty n) ≠ c := by
  simp [entropyLabelA, b, c]

theorem AuxForm_finset_ne {n : ℕ} {x y : entropyParty n} (h : x ≠ y) :
    ({x} : Finset (entropyParty n)) ≠ {x, y} := by
  intro hf
  have : y ∈ ({x} : Finset (entropyParty n)) := by
    have : y ∈ ({x, y} : Finset (entropyParty n)) := by simp
    simpa [hf] using this
  simp [h.symm] at this

theorem AuxForm_pair_eq_union {n : ℕ} (x y : entropyParty n) :
    ({x, y} : Finset (entropyParty n)) = {x} ∪ {y} := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, or_comm]

theorem AuxForm_triple_eq_union {n : ℕ} (x y z : entropyParty n) :
    ({x, y, z} : Finset (entropyParty n)) = {x} ∪ {y} ∪ {z} := by
  ext w
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
    or_comm, or_left_comm, or_assoc]

theorem AuxForm_IACB_at_B {n : ℕ} :
    cmiForm ({entropyLabelA} : Finset (entropyParty n)) {c} {b} {b} = -1 := by
  have hA : (entropyLabelA : entropyParty n) ≠ b := (AuxForm_labels_ne (n := n)).1
  have hC : (c : entropyParty n) ≠ b := (AuxForm_labels_ne (n := n)).2.2.symm
  have hb : ({b} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
  have hab : ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => hb (Finset.union_eq_empty.mp h).2
  have hcb : ({c} ∪ {b} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => hb (Finset.union_eq_empty.mp h).2
  have habc : ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) ≠ ∅ := by
    intro h
    have hmem : (b : entropyParty n) ∈
        ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    exact Finset.notMem_empty _ (h ▸ hmem)
  have nAB : ({b} : Finset (entropyParty n)) ≠ {entropyLabelA} ∪ {b} := by
    intro h
    have hmem : (entropyLabelA : entropyParty n) ∈
        ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    rw [← h] at hmem
    exact hA (Finset.mem_singleton.mp hmem)
  have nCB : ({b} : Finset (entropyParty n)) ≠ {c} ∪ {b} := by
    intro h
    have hmem : (c : entropyParty n) ∈ ({c} ∪ {b} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    rw [← h] at hmem
    exact hC (Finset.mem_singleton.mp hmem)
  have nABC : ({b} : Finset (entropyParty n)) ≠ {entropyLabelA} ∪ {c} ∪ {b} := by
    intro h
    have hmem : (entropyLabelA : entropyParty n) ∈
        ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))
    rw [← h] at hmem
    exact hA (Finset.mem_singleton.mp hmem)
  unfold cmiForm
  simp only [Pi.add_apply, Pi.sub_apply, AuxForm_atom_apply,
    hb, hab, hcb, habc, nAB, nCB, nABC, ite_true, ite_false]
  norm_num

theorem AuxForm_IBCA_at_A {n : ℕ} :
    cmiForm ({b} : Finset (entropyParty n)) {c} {entropyLabelA} {entropyLabelA} = -1 := by
  have hA : (entropyLabelA : entropyParty n) ≠ b := (AuxForm_labels_ne (n := n)).1
  have hC : (c : entropyParty n) ≠ entropyLabelA := (AuxForm_labels_ne (n := n)).2.1.symm
  have ha : ({entropyLabelA} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
  have hab : ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => ha (Finset.union_eq_empty.mp h).2
  have hac : ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => ha (Finset.union_eq_empty.mp h).2
  have habc : ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) ≠ ∅ := by
    intro h
    have hmem : (entropyLabelA : entropyParty n) ∈
        ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    exact Finset.notMem_empty _ (h ▸ hmem)
  have nBA : ({entropyLabelA} : Finset (entropyParty n)) ≠ {b} ∪ {entropyLabelA} := by
    intro h
    have hmem : (b : entropyParty n) ∈ ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    rw [← h] at hmem
    exact hA (Finset.mem_singleton.mp hmem).symm
  have nCA : ({entropyLabelA} : Finset (entropyParty n)) ≠ {c} ∪ {entropyLabelA} := by
    intro h
    have hmem : (c : entropyParty n) ∈ ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    rw [← h] at hmem
    exact hC (Finset.mem_singleton.mp hmem)
  have nBCA : ({entropyLabelA} : Finset (entropyParty n)) ≠ {b} ∪ {c} ∪ {entropyLabelA} := by
    intro h
    have hmem : (b : entropyParty n) ∈
        ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))
    rw [← h] at hmem
    exact hA (Finset.mem_singleton.mp hmem).symm
  unfold cmiForm
  simp only [Pi.add_apply, Pi.sub_apply, AuxForm_atom_apply,
    ha, hab, hac, habc, nBA, nCA, nBCA, ite_true, ite_false]
  norm_num



theorem AuxForm_IACB_ne_zero {n : ℕ} :
    cmiForm ({entropyLabelA} : Finset (entropyParty n)) {c} {b} ≠ 0 := by
  intro h
  have := congrFun h {b}
  simp [AuxForm_IACB_at_B] at this

theorem AuxForm_IBCA_ne_zero {n : ℕ} :
    cmiForm ({b} : Finset (entropyParty n)) {c} {entropyLabelA} ≠ 0 := by
  intro h
  have := congrFun h {entropyLabelA}
  simp [AuxForm_IBCA_at_A] at this

theorem AuxForm_mem_constraints {n : ℕ} {L : Form (entropyParty n)} :
    L ∈ constraints n ↔
      L = cmiForm {entropyLabelA} {c} {b} ∨ L = cmiForm {b} {c} {entropyLabelA} := by
  simp [constraints]

theorem AuxSE_isX_of_disj_ABC {n : ℕ} {W : Finset (entropyParty n)}
    (h : Disjoint W {entropyLabelA, b, c}) : AuxSE_isX W := by
  intro y hy
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
  rcases y with j | i
  · have : Sum.inl j ∈ ({entropyLabelA, b, c} : Finset (entropyParty n)) := by
      fin_cases j <;> simp [entropyLabelA, b, c]
    exact (Finset.disjoint_left.mp h hy this).elim
  · exact ⟨i, rfl⟩

theorem AuxForm_family_symm {P : Type*} [Fintype P] [DecidableEq P] {p : ℕ}
    (U V W : Finset P) (alpha : Fin p → Finset P) :
    familyForm U V W alpha = familyForm V U W alpha := by
  unfold familyForm
  have hc : (∑ i, cmiForm U V (alpha i)) = ∑ i, cmiForm V U (alpha i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    ext S
    unfold cmiForm
    simp [Finset.union_comm U V, add_comm]
  have hm : miForm (U ∪ V) W = miForm (V ∪ U) W := by
    unfold miForm; simp [Finset.union_comm U V]
  rw [hc, hm]

theorem AuxWitness_family_deg {n p : ℕ} (hn : 2 ≤ n)
    {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (hInst : DisjointInstance U V W alpha)
    (hdeg : W = ∅ ∨ (U = ∅ ∧ V = ∅)) :
    0 ≤ evaluateEntropyForm (familyForm U V W alpha) (AuxWitness n) := by
  have hUV := AuxInst_disjUV hInst
  have hUW := AuxInst_disjUW hInst
  have hVW := AuxInst_disjVW hInst
  have hαdis : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j) := hInst.2.2
  have h0 : AuxWitness n (∅ : Finset (entropyParty n)) = 0 := by
    have hx : xCount (∅ : Finset (entropyParty n)) = 0 := by simp [xCount]
    rw [AuxWitness, AuxSE_f0, hx]; simp
  rcases hdeg with hW | ⟨hU, hV⟩
  · subst hW
    have ev : evaluateEntropyForm (familyForm U V ∅ alpha) (AuxWitness n) =
        (∑ i, evaluateEntropyForm (cmiForm U V (alpha i)) (AuxWitness n)) +
          (∑ i, AuxWitness n (alpha i)) - AuxWitness n (Finset.univ.biUnion alpha) := by
      unfold familyForm
      rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add, AuxSE_ev_sum, AuxSE_ev_sum,
          AuxSE_ev_smul]
      have hMI : evaluateEntropyForm (miForm (U ∪ V) (∅ : Finset (entropyParty n)))
          (AuxWitness n) = 0 := by
        rw [AuxSE_ev_mi (U ∪ V) ∅ (AuxWitness n) h0]
        simp [h0]
      have hA : ∀ i, evaluateEntropyForm (entropyAtom (alpha i)) (AuxWitness n) =
          AuxWitness n (alpha i) := fun i => AuxSE_ev_atom' _ _ h0
      have hU' : evaluateEntropyForm (entropyAtom (Finset.univ.biUnion alpha))
          (AuxWitness n) = AuxWitness n (Finset.univ.biUnion alpha) :=
        AuxSE_ev_atom' _ _ h0
      simp [hMI, hA, hU', smul_eq_mul]
    rw [ev]
    have hI : ∀ i, 0 ≤ evaluateEntropyForm (cmiForm U V (alpha i)) (AuxWitness n) := by
      intro i
      have hi := AuxInst_disj_alpha hInst i
      exact AuxWitness_cmi_nonneg n hn hUV hi.1 hi.2.1
    have hsumI : 0 ≤ ∑ i, evaluateEntropyForm (cmiForm U V (alpha i)) (AuxWitness n) :=
      Finset.sum_nonneg fun i _ => hI i
    linarith [AuxWitness_sum_alpha (n := n) (p := p) hn hαdis]
  · subst hU; subst hV
    -- familyForm ∅ ∅ W alpha = ∑ 0 + ∑ S(alpha) - S(union) - ((p)-1) • miForm ∅ W
    have ev : evaluateEntropyForm (familyForm ∅ ∅ W alpha) (AuxWitness n) =
        (∑ i, AuxWitness n (alpha i)) - AuxWitness n (Finset.univ.biUnion alpha) := by
      unfold familyForm
      rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add, AuxSE_ev_sum, AuxSE_ev_sum,
          AuxSE_ev_smul]
      have hI : ∀ i, evaluateEntropyForm (cmiForm (∅ : Finset (entropyParty n)) ∅ (alpha i))
          (AuxWitness n) = 0 := by
        intro i
        rw [AuxForm_cmi_zero_emptyU, AuxSE_ev_zero]
      have hMI : evaluateEntropyForm (miForm (∅ : Finset (entropyParty n)) W)
          (AuxWitness n) = 0 := by
        rw [AuxSE_ev_mi (∅ : Finset (entropyParty n)) W (AuxWitness n) h0]
        simp [h0]
      have hMI' : evaluateEntropyForm (miForm (∅ ∪ ∅) W) (AuxWitness n) = 0 := by
        simpa using hMI
      have hA : ∀ i, evaluateEntropyForm (entropyAtom (alpha i)) (AuxWitness n) =
          AuxWitness n (alpha i) := fun i => AuxSE_ev_atom' _ _ h0
      have hUn : evaluateEntropyForm (entropyAtom (Finset.univ.biUnion alpha))
          (AuxWitness n) = AuxWitness n (Finset.univ.biUnion alpha) :=
        AuxSE_ev_atom' _ _ h0
      simp [hI, hMI, hMI', hA, hUn, smul_eq_mul]
    rw [ev]
    linarith [AuxWitness_sum_alpha (n := n) (p := p) hn hαdis]

theorem AuxForm_cmi_apply {P : Type*} [DecidableEq P] (U V W S : Finset P) :
    cmiForm U V W S =
      (if U ∪ W = ∅ then (0 : ℝ) else if S = U ∪ W then 1 else 0) +
      (if V ∪ W = ∅ then (0 : ℝ) else if S = V ∪ W then 1 else 0) -
      (if W = ∅ then (0 : ℝ) else if S = W then 1 else 0) -
      (if U ∪ V ∪ W = ∅ then (0 : ℝ) else if S = U ∪ V ∪ W then 1 else 0) := by
  unfold cmiForm
  simp only [Pi.add_apply, Pi.sub_apply, AuxForm_atom_apply]

theorem AuxForm_mi_apply {P : Type*} [DecidableEq P] (U V S : Finset P) :
    miForm U V S =
      (if U = ∅ then (0 : ℝ) else if S = U then 1 else 0) +
      (if V = ∅ then (0 : ℝ) else if S = V then 1 else 0) -
      (if U ∪ V = ∅ then (0 : ℝ) else if S = U ∪ V then 1 else 0) := by
  unfold miForm
  simp only [Pi.add_apply, Pi.sub_apply, AuxForm_atom_apply]

theorem AuxForm_cmi_empty_cond {P : Type*} [DecidableEq P] (U V : Finset P) :
    cmiForm U V (∅ : Finset P) = miForm U V := by
  ext S
  rw [AuxForm_cmi_apply, AuxForm_mi_apply]
  simp [Finset.union_empty]

theorem AuxForm_cmi_symm {P : Type*} [DecidableEq P] (U V W : Finset P) :
    cmiForm U V W = cmiForm V U W := by
  ext S
  unfold cmiForm
  simp [Finset.union_comm U V, add_comm]

theorem AuxForm_bit_nonneg (p q : Prop) [Decidable p] [Decidable q] :
    (0 : ℝ) ≤ (if p then (0 : ℝ) else if q then 1 else 0) := by
  split_ifs <;> norm_num

theorem AuxForm_bit_le_one (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (0 : ℝ) else if q then 1 else 0) ≤ (1 : ℝ) := by
  split_ifs <;> norm_num

theorem AuxForm_disjoint_singleton {n : ℕ} {U : Finset (entropyParty n)}
    {px : entropyParty n} (h : Disjoint U {px}) : px ∉ U :=
  Finset.disjoint_singleton_right.mp h

theorem AuxForm_pair_ne_of_left {n : ℕ} {px py pz : entropyParty n}
    (hxy : px ≠ py) (hxz : px ≠ pz) :
    ({px} ∪ {pz} : Finset (entropyParty n)) ≠ {py} ∪ {pz} := by
  intro h
  have hx : px ∈ ({py} ∪ {pz} : Finset (entropyParty n)) := by
    have : px ∈ ({px} ∪ {pz} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    exact h ▸ this
  rcases Finset.mem_union.mp hx with hx' | hz
  · exact hxy (Finset.mem_singleton.mp hx')
  · exact hxz (Finset.mem_singleton.mp hz)

theorem AuxForm_pair_ne_singleton {n : ℕ} {px pz : entropyParty n} (hxz : px ≠ pz) :
    ({px} ∪ {pz} : Finset (entropyParty n)) ≠ {pz} := by
  intro h
  have hx : px ∈ ({pz} : Finset (entropyParty n)) := by
    have : px ∈ ({px} ∪ {pz} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    exact h ▸ this
  exact hxz (Finset.mem_singleton.mp hx)

theorem AuxForm_pair_ne_triple {n : ℕ} {px py pz : entropyParty n}
    (hyz : py ≠ pz) (hyx : py ≠ px) :
    ({px} ∪ {pz} : Finset (entropyParty n)) ≠ {px} ∪ {py} ∪ {pz} := by
  intro h
  have hy : py ∈ ({px} ∪ {pz} : Finset (entropyParty n)) := by
    have : py ∈ ({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))))
    rw [← h] at this; exact this
  rcases Finset.mem_union.mp hy with hx | hz
  · exact hyx (Finset.mem_singleton.mp hx)
  · exact hyz (Finset.mem_singleton.mp hz)

theorem AuxForm_singleton_ne_triple {n : ℕ} {px py pz : entropyParty n} (hxz : px ≠ pz) :
    ({pz} : Finset (entropyParty n)) ≠ {px} ∪ {py} ∪ {pz} := by
  intro h
  have hpx : px ∈ ({pz} : Finset (entropyParty n)) := by
    have : px ∈ ({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))
    rw [← h] at this; exact this
  exact hxz (Finset.mem_singleton.mp hpx)

theorem AuxForm_labels_disjoint {n : ℕ} {px py : entropyParty n} (h : px ≠ py) :
    Disjoint ({px} : Finset (entropyParty n)) {py} := by
  simp [Finset.disjoint_singleton, h]

theorem AuxForm_std_trip {n : ℕ} {px py pz : entropyParty n}
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz) :
    DisjointTriple ({px} : Finset (entropyParty n)) {py} {pz} :=
  ⟨AuxForm_labels_disjoint hxy, AuxForm_labels_disjoint hxz, AuxForm_labels_disjoint hyz⟩

theorem AuxForm_std_ne_zero {n : ℕ} {px py pz : entropyParty n}
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz) :
    cmiForm ({px} : Finset (entropyParty n)) {py} {pz} ≠ 0 := by
  intro h0
  have := (AuxForm_cmi_eq_zero_of_triple (AuxForm_std_trip hxy hxz hyz)).mp h0
  simp [Finset.singleton_ne_empty] at this

theorem AuxForm_std_at_cond {n : ℕ} {px py pz : entropyParty n}
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz) :
    cmiForm ({px} : Finset (entropyParty n)) {py} {pz} {pz} = -1 := by
  have hz : ({pz} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
  have hxzN : ({px} ∪ {pz} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => hz (Finset.union_eq_empty.mp h).2
  have hyzN : ({py} ∪ {pz} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => hz (Finset.union_eq_empty.mp h).2
  have hxyzN : ({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) ≠ ∅ := by
    intro h
    have : pz ∈ ({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    exact Finset.notMem_empty _ (h ▸ this)
  have nXZ : ({pz} : Finset (entropyParty n)) ≠ {px} ∪ {pz} :=
    (AuxForm_pair_ne_singleton hxz).symm
  have nYZ : ({pz} : Finset (entropyParty n)) ≠ {py} ∪ {pz} :=
    (AuxForm_pair_ne_singleton hyz).symm
  have nXYZ : ({pz} : Finset (entropyParty n)) ≠ {px} ∪ {py} ∪ {pz} :=
    AuxForm_singleton_ne_triple hxz
  rw [AuxForm_cmi_apply]
  simp only [hxzN, hyzN, hz, hxyzN, nXZ, nYZ, nXYZ, ite_true, ite_false]
  norm_num

theorem AuxForm_union_singleton_of_pair {n : ℕ}
    {U : Finset (entropyParty n)} {px py : entropyParty n}
    (hxU : px ∉ U) (hU : U ≠ ∅) (heq : U ∪ {px} = {py} ∪ {px}) :
    U = {py} := by
  have hyU : py ∈ U := by
    have : py ∈ U ∪ {px} := by
      rw [heq]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    rcases Finset.mem_union.mp this with hy | hx
    · exact hy
    · have hyx : py = px := Finset.mem_singleton.mp hx
      have heq' : U ∪ {px} = ({px} : Finset (entropyParty n)) := by
        rw [hyx] at heq
        simpa using heq
      have hUsub : U ⊆ ({px} : Finset (entropyParty n)) := by
        intro t ht
        have ht' : t ∈ U ∪ {px} := Finset.mem_union.mpr (Or.inl ht)
        rw [heq'] at ht'
        exact ht'
      have hUemp : U = ∅ := by
        ext t
        constructor
        · intro ht
          have htpx : t = px := Finset.mem_singleton.mp (hUsub ht)
          rw [htpx] at ht
          exact (hxU ht).elim
        · intro ht
          exact (Finset.notMem_empty t ht).elim
      exact (hU hUemp).elim
  ext t
  constructor
  · intro ht
    have ht' : t ∈ U ∪ {px} := Finset.mem_union.mpr (Or.inl ht)
    rw [heq] at ht'
    rcases Finset.mem_union.mp ht' with hy | hx
    · exact hy
    · have : t = px := Finset.mem_singleton.mp hx
      subst this
      exact (hxU ht).elim
  · intro ht
    have : t = py := Finset.mem_singleton.mp ht
    subst this
    exact hyU

theorem AuxForm_std_at_support {n : ℕ} {px py pz : entropyParty n}
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz)
    (S : Finset (entropyParty n)) :
    cmiForm ({px} : Finset (entropyParty n)) {py} {pz} S =
      (if S = {px} ∪ {pz} then (1 : ℝ) else 0) +
      (if S = {py} ∪ {pz} then 1 else 0) -
      (if S = {pz} then 1 else 0) -
      (if S = {px} ∪ {py} ∪ {pz} then 1 else 0) := by
  have hz : ({pz} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
  have hxzN : ({px} ∪ {pz} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => hz (Finset.union_eq_empty.mp h).2
  have hyzN : ({py} ∪ {pz} : Finset (entropyParty n)) ≠ ∅ :=
    fun h => hz (Finset.union_eq_empty.mp h).2
  have hxyzN : ({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) ≠ ∅ := by
    intro h
    have : pz ∈ ({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    exact Finset.notMem_empty _ (h ▸ this)
  rw [AuxForm_cmi_apply]
  simp only [hxzN, hyzN, hz, hxyzN, ite_false]

theorem AuxForm_std_eq_one {n : ℕ} {px py pz : entropyParty n}
    {S : Finset (entropyParty n)}
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz)
    (h : cmiForm ({px} : Finset (entropyParty n)) {py} {pz} S = 1) :
    S = {px} ∪ {pz} ∨ S = {py} ∪ {pz} := by
  have hsup := AuxForm_std_at_support hxy hxz hyz S
  rw [hsup] at h
  by_cases hxS : S = {px} ∪ {pz}
  · exact Or.inl hxS
  · by_cases hyS : S = {py} ∪ {pz}
    · exact Or.inr hyS
    · by_cases hzS : S = {pz}
      · subst hzS
        have n1 : ¬ ({pz} = {px} ∪ {pz}) := hxS
        have n2 : ¬ ({pz} = {py} ∪ {pz}) := hyS
        have n3 : ¬ ({pz} = {px} ∪ {py} ∪ {pz}) := AuxForm_singleton_ne_triple hxz
        simp only [n1, n2, n3, ite_true, ite_false] at h
        norm_num at h
      · by_cases htS : S = {px} ∪ {py} ∪ {pz}
        · subst htS
          have n1 : ¬ (({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) = {px} ∪ {pz}) := by
            intro h'
            exact (AuxForm_pair_ne_triple hyz hxy.symm) h'.symm
          have n2 : ¬ (({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) = {py} ∪ {pz}) := by
            intro h'
            have hne : ({py} ∪ {pz} : Finset (entropyParty n)) ≠ {py} ∪ {px} ∪ {pz} :=
              AuxForm_pair_ne_triple hxz hxy
            have hcomm : ({py} ∪ {px} ∪ {pz} : Finset (entropyParty n)) =
                {px} ∪ {py} ∪ {pz} := by
              ext t
              simp only [Finset.mem_union, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
            exact hne (h'.symm.trans hcomm.symm)
          have n3 : ¬ (({px} ∪ {py} ∪ {pz} : Finset (entropyParty n)) = {pz}) := hzS
          simp only [n1, n2, n3, ite_true, ite_false] at h
          norm_num at h
        · simp only [hxS, hyS, hzS, htS, ite_true, ite_false] at h
          norm_num at h


theorem AuxForm_mi_ne_std {n : ℕ} {V W : Finset (entropyParty n)}
    {px py pz : entropyParty n}
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz)
    (heq : miForm V W = cmiForm ({px} : Finset (entropyParty n)) {py} {pz}) : False := by
  have hL : miForm V W {pz} = -1 := by
    have := congrFun heq {pz}
    simpa [AuxForm_std_at_cond hxy hxz hyz] using this
  rw [AuxForm_mi_apply] at hL
  set a := (if V = ∅ then (0 : ℝ) else if {pz} = V then 1 else 0)
  set b := (if W = ∅ then (0 : ℝ) else if {pz} = W then 1 else 0)
  set c := (if V ∪ W = ∅ then (0 : ℝ) else if {pz} = V ∪ W then 1 else 0)
  have habc : a + b - c = -1 := hL
  have ha0 : 0 ≤ a := AuxForm_bit_nonneg (V = ∅) ({pz} = V)
  have hb0 : 0 ≤ b := AuxForm_bit_nonneg (W = ∅) ({pz} = W)
  have hc1 : c ≤ 1 := AuxForm_bit_le_one (V ∪ W = ∅) ({pz} = V ∪ W)
  have hc : c = 1 := le_antisymm hc1 (by linarith)
  have ha : a = 0 := le_antisymm (by linarith) ha0
  have hb : b = 0 := le_antisymm (by linarith) hb0
  have hUn : {pz} = V ∪ W := by
    have hne : V ∪ W ≠ ∅ := by
      intro hE
      have : c = 0 := by simp only [c, hE, ite_true]
      exact zero_ne_one (this.symm.trans hc)
    have : {pz} = V ∪ W := by
      by_contra hne'
      have : c = 0 := by simp only [c, hne, hne', ite_true, ite_false]
      exact zero_ne_one (this.symm.trans hc)
    exact this
  have hVsub : V ⊆ ({pz} : Finset (entropyParty n)) := by
    intro t ht
    have : t ∈ V ∪ W := Finset.mem_union.mpr (Or.inl ht)
    simpa [hUn] using this
  have hWsub : W ⊆ ({pz} : Finset (entropyParty n)) := by
    intro t ht
    have : t ∈ V ∪ W := Finset.mem_union.mpr (Or.inr ht)
    simpa [hUn] using this
  have hV0 : V = ∅ := by
    by_cases hVemp : V = ∅
    · exact hVemp
    · have hVz : V = {pz} := by
        ext t
        constructor
        · intro ht; exact hVsub ht
        · intro ht
          have htpz : t = pz := Finset.mem_singleton.mp ht
          obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hVemp
          have hupz : u = pz := Finset.mem_singleton.mp (hVsub hu)
          rw [htpz, ← hupz]
          exact hu
      have : a = 1 := by
        have hne : V ≠ ∅ := hVemp
        simp only [a, hne, hVz, ite_true, ite_false]
        have : ({pz} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
        simp [this]
      exact (zero_ne_one (ha.symm.trans this)).elim
  have hW0 : W = ∅ := by
    by_cases hWemp : W = ∅
    · exact hWemp
    · have hWz : W = {pz} := by
        ext t
        constructor
        · intro ht; exact hWsub ht
        · intro ht
          have htpz : t = pz := Finset.mem_singleton.mp ht
          obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hWemp
          have hupz : u = pz := Finset.mem_singleton.mp (hWsub hu)
          rw [htpz, ← hupz]
          exact hu
      have : b = 1 := by
        have hne : W ≠ ∅ := hWemp
        simp only [b, hne, hWz, ite_true, ite_false]
        have : ({pz} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
        simp [this]
      exact (zero_ne_one (hb.symm.trans this)).elim
  have : V ∪ W = (∅ : Finset (entropyParty n)) := by simp [hV0, hW0]
  exact (Finset.singleton_ne_empty pz) (hUn.trans this)


theorem AuxForm_two_nonempty_disjoint_card {n : ℕ}
    {U W : Finset (entropyParty n)}
    (hU : U ≠ ∅) (hW : W ≠ ∅) (hUW : Disjoint U W) :
    2 ≤ (U ∪ W).card := by
  have hcard := Finset.card_union_of_disjoint hUW
  have hU1 : 1 ≤ U.card := Nat.succ_le_of_lt (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU))
  have hW1 : 1 ≤ W.card := Nat.succ_le_of_lt (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW))
  omega

theorem AuxForm_union_ne_singleton {n : ℕ}
    {U W V : Finset (entropyParty n)} {pz : entropyParty n}
    (hU : U ≠ ∅) (hW : W ≠ ∅) (hUW : Disjoint U W) :
    U ∪ W ∪ V ≠ {pz} := by
  intro h
  have hsub : U ∪ W ⊆ ({pz} : Finset (entropyParty n)) := by
    intro t ht
    have : t ∈ U ∪ W ∪ V := Finset.mem_union.mpr (Or.inl ht)
    exact h ▸ this
  have hle : (U ∪ W).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hge : 2 ≤ (U ∪ W).card := AuxForm_two_nonempty_disjoint_card hU hW hUW
  omega

theorem AuxForm_left_union_ne_cond {n : ℕ}
    {U : Finset (entropyParty n)} {pz : entropyParty n}
    (hU : U ≠ ∅) (hzU : pz ∉ U) :
    U ∪ {pz} ≠ {pz} := by
  intro h
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hU
  have : a ∈ ({pz} : Finset (entropyParty n)) := by
    have : a ∈ U ∪ {pz} := Finset.mem_union.mpr (Or.inl ha)
    exact h ▸ this
  have hapz : a = pz := Finset.mem_singleton.mp this
  rw [hapz] at ha
  exact hzU ha

theorem AuxForm_left_union_ne_right {n : ℕ}
    {U W : Finset (entropyParty n)} {pz : entropyParty n}
    (hU : U ≠ ∅) (hUW : Disjoint U W) (hzU : pz ∉ U) :
    U ∪ {pz} ≠ W ∪ {pz} := by
  intro h
  have hUsub : U ⊆ W ∪ {pz} := by
    intro t ht
    have : t ∈ U ∪ {pz} := Finset.mem_union.mpr (Or.inl ht)
    exact h ▸ this
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hU
  rcases Finset.mem_union.mp (hUsub ha) with haW | haz
  · exact Finset.disjoint_left.mp hUW ha haW
  · exact hzU (by simpa using (Finset.mem_singleton.mp haz) ▸ ha)

theorem AuxForm_left_union_ne_big {n : ℕ}
    {U W : Finset (entropyParty n)} {pz : entropyParty n}
    (hW : W ≠ ∅) (hUW : Disjoint U W) (hzW : pz ∉ W) :
    U ∪ {pz} ≠ U ∪ W ∪ {pz} := by
  intro h
  have hWsub : W ⊆ U ∪ {pz} := by
    intro t ht
    have : t ∈ U ∪ W ∪ {pz} :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ht)))
    rw [← h] at this; exact this
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hW
  rcases Finset.mem_union.mp (hWsub ha) with haU | haz
  · exact Finset.disjoint_left.mp hUW haU ha
  · exact hzW (by simpa using (Finset.mem_singleton.mp haz) ▸ ha)

theorem AuxForm_cmi_at_left_union {n : ℕ}
    {U W : Finset (entropyParty n)} {pz : entropyParty n}
    (hU : U ≠ ∅) (hW : W ≠ ∅) (hUW : Disjoint U W)
    (hzU : pz ∉ U) (hzW : pz ∉ W) :
    cmiForm U W {pz} (U ∪ {pz}) = 1 := by
  have hUVN : U ∪ {pz} ≠ ∅ := fun h => hU (Finset.union_eq_empty.mp h).1
  have hWVN : W ∪ {pz} ≠ ∅ := fun h => hW (Finset.union_eq_empty.mp h).1
  have hzN : ({pz} : Finset (entropyParty n)) ≠ ∅ := Finset.singleton_ne_empty _
  have hbigN : U ∪ W ∪ {pz} ≠ ∅ := by
    intro hE
    exact hU (Finset.union_eq_empty.mp (Finset.union_eq_empty.mp hE).1).1
  have n1 : U ∪ {pz} ≠ {pz} := AuxForm_left_union_ne_cond hU hzU
  have n2 : U ∪ {pz} ≠ W ∪ {pz} := AuxForm_left_union_ne_right hU hUW hzU
  have n3 : U ∪ {pz} ≠ U ∪ W ∪ {pz} := AuxForm_left_union_ne_big hW hUW hzW
  rw [AuxForm_cmi_apply]
  simp only [hUVN, hWVN, hzN, hbigN, n1, n2, n3, ite_true, ite_false]
  norm_num

theorem AuxForm_cmi_at_right_union {n : ℕ}
    {U W : Finset (entropyParty n)} {pz : entropyParty n}
    (hU : U ≠ ∅) (hW : W ≠ ∅) (hUW : Disjoint U W)
    (hzU : pz ∉ U) (hzW : pz ∉ W) :
    cmiForm U W {pz} (W ∪ {pz}) = 1 := by
  have hswap : cmiForm U W {pz} = cmiForm W U {pz} := AuxForm_cmi_symm U W {pz}
  rw [hswap]
  exact AuxForm_cmi_at_left_union hW hU hUW.symm hzW hzU

theorem AuxForm_cmi_eq_std {n : ℕ} {U W V : Finset (entropyParty n)}
    {px py pz : entropyParty n}
    (htrip : DisjointTriple U W V)
    (hxy : px ≠ py) (hxz : px ≠ pz) (hyz : py ≠ pz)
    (heq : cmiForm U W V = cmiForm ({px} : Finset (entropyParty n)) {py} {pz}) :
    V = {pz} ∧ ((U = {px} ∧ W = {py}) ∨ (U = {py} ∧ W = {px})) := by
  have hUne : U ≠ ∅ := by
    intro hU
    have h0 : cmiForm U W V = 0 := by
      subst hU; exact AuxForm_cmi_zero_emptyU W V
    exact AuxForm_std_ne_zero hxy hxz hyz (heq.symm.trans h0)
  have hWne : W ≠ ∅ := by
    intro hW
    have h0 : cmiForm U W V = 0 := by
      subst hW; exact AuxForm_cmi_zero_emptyV U V
    exact AuxForm_std_ne_zero hxy hxz hyz (heq.symm.trans h0)
  have hval : cmiForm U W V {pz} = -1 := by
    have := congrFun heq {pz}
    simpa [AuxForm_std_at_cond hxy hxz hyz] using this
  have hUV : Disjoint U V := htrip.2.1
  have hWV : Disjoint W V := htrip.2.2
  have hUW : Disjoint U W := htrip.1
  have hVeq : V = {pz} := by
    by_cases hVs : V = {pz}
    · exact hVs
    · have hbig : U ∪ W ∪ V ≠ {pz} :=
        AuxForm_union_ne_singleton hUne hWne hUW
      rw [AuxForm_cmi_apply] at hval
      have hVterm : (if V = ∅ then (0 : ℝ) else if {pz} = V then 1 else 0) = 0 := by
        by_cases hV0 : V = ∅
        · simp only [hV0, ite_true]
        · have : ¬ {pz} = V := fun h => hVs h.symm
          simp only [hV0, this, ite_true, ite_false]
      have hBterm :
          (if U ∪ W ∪ V = ∅ then (0 : ℝ) else if {pz} = U ∪ W ∪ V then 1 else 0) = 0 := by
        have hne : U ∪ W ∪ V ≠ ∅ := by
          intro hE
          exact hUne (Finset.union_eq_empty.mp (Finset.union_eq_empty.mp hE).1).1
        have : ¬ {pz} = U ∪ W ∪ V := fun h => hbig h.symm
        simp only [hne, this, ite_true, ite_false]
      have hplus :
          0 ≤
            (if U ∪ V = ∅ then (0 : ℝ) else if {pz} = U ∪ V then 1 else 0) +
            (if W ∪ V = ∅ then (0 : ℝ) else if {pz} = W ∪ V then 1 else 0) :=
        add_nonneg (AuxForm_bit_nonneg (U ∪ V = ∅) ({pz} = U ∪ V))
          (AuxForm_bit_nonneg (W ∪ V = ∅) ({pz} = W ∪ V))
      simp only [hVterm, hBterm, sub_zero] at hval
      linarith
  subst hVeq
  have hzU : pz ∉ U := AuxForm_disjoint_singleton hUV
  have hzW : pz ∉ W := AuxForm_disjoint_singleton hWV
  have hUor : U ∪ {pz} = {px} ∪ {pz} ∨ U ∪ {pz} = {py} ∪ {pz} := by
    have hcoef := AuxForm_cmi_at_left_union hUne hWne hUW hzU hzW
    have := congrFun heq (U ∪ {pz})
    have hR : cmiForm ({px} : Finset (entropyParty n)) {py} {pz} (U ∪ {pz}) = 1 :=
      this.symm.trans hcoef
    exact AuxForm_std_eq_one hxy hxz hyz hR
  have hWor : W ∪ {pz} = {px} ∪ {pz} ∨ W ∪ {pz} = {py} ∪ {pz} := by
    have hcoef := AuxForm_cmi_at_right_union hUne hWne hUW hzU hzW
    have := congrFun heq (W ∪ {pz})
    have hR : cmiForm ({px} : Finset (entropyParty n)) {py} {pz} (W ∪ {pz}) = 1 :=
      this.symm.trans hcoef
    exact AuxForm_std_eq_one hxy hxz hyz hR
  have hUW_ne : U ∪ {pz} ≠ W ∪ {pz} := AuxForm_left_union_ne_right hUne hUW hzU
  rcases hUor with hUx | hUy
  · have hU : U = {px} := AuxForm_union_singleton_of_pair hzU hUne hUx
    have hWy : W ∪ {pz} = {py} ∪ {pz} := by
      rcases hWor with hWx | hWy
      · exact (hUW_ne (hUx.trans hWx.symm)).elim
      · exact hWy
    exact ⟨rfl, Or.inl ⟨hU, AuxForm_union_singleton_of_pair hzW hWne hWy⟩⟩
  · have hU : U = {py} := AuxForm_union_singleton_of_pair hzU hUne hUy
    have hWx : W ∪ {pz} = {px} ∪ {pz} := by
      rcases hWor with hWx | hWy
      · exact hWx
      · exact (hUW_ne (hUy.trans hWy.symm)).elim
    exact ⟨rfl, Or.inr ⟨hU, AuxForm_union_singleton_of_pair hzW hWne hWx⟩⟩


theorem AuxForm_IACB_at_C {n : ℕ} :
    cmiForm ({entropyLabelA} : Finset (entropyParty n)) {c} {b} {c} = 0 := by
  have hA := (AuxForm_labels_ne (n := n)).1
  have hAC := (AuxForm_labels_ne (n := n)).2.1
  have hBC := (AuxForm_labels_ne (n := n)).2.2
  rw [AuxForm_std_at_support hAC hA hBC.symm]
  have n1 : ({c} : Finset (entropyParty n)) ≠ {entropyLabelA} ∪ {b} := by
    intro h
    have : (entropyLabelA : entropyParty n) ∈ ({c} : Finset (entropyParty n)) := by
      have hx : entropyLabelA ∈ ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
      rw [← h] at hx; exact hx
    exact hAC (Finset.mem_singleton.mp this)
  have n2 : ({c} : Finset (entropyParty n)) ≠ {c} ∪ {b} := by
    intro h
    have : (b : entropyParty n) ∈ ({c} : Finset (entropyParty n)) := by
      have hx : b ∈ ({c} ∪ {b} : Finset (entropyParty n)) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
      rw [← h] at hx; exact hx
    exact hBC (Finset.mem_singleton.mp this)
  have n3 : ({c} : Finset (entropyParty n)) ≠ {b} := by
    intro h
    exact hBC (Finset.singleton_inj.mp h).symm
  have n4 : ({c} : Finset (entropyParty n)) ≠ {entropyLabelA} ∪ {c} ∪ {b} := by
    intro h
    have : (entropyLabelA : entropyParty n) ∈ ({c} : Finset (entropyParty n)) := by
      have hx : entropyLabelA ∈ ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))
      rw [← h] at hx; exact hx
    exact hAC (Finset.mem_singleton.mp this)
  simp only [n1, n2, n3, n4, ite_true, ite_false]
  norm_num

theorem AuxForm_IBCA_at_C {n : ℕ} :
    cmiForm ({b} : Finset (entropyParty n)) {c} {entropyLabelA} {c} = 0 := by
  have hA := (AuxForm_labels_ne (n := n)).1
  have hAC := (AuxForm_labels_ne (n := n)).2.1
  have hBC := (AuxForm_labels_ne (n := n)).2.2
  rw [AuxForm_std_at_support hBC hA.symm hAC.symm]
  have n1 : ({c} : Finset (entropyParty n)) ≠ {b} ∪ {entropyLabelA} := by
    intro h
    have : (b : entropyParty n) ∈ ({c} : Finset (entropyParty n)) := by
      have hx : b ∈ ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
      rw [← h] at hx; exact hx
    exact hBC (Finset.mem_singleton.mp this)
  have n2 : ({c} : Finset (entropyParty n)) ≠ {c} ∪ {entropyLabelA} := by
    intro h
    have : (entropyLabelA : entropyParty n) ∈ ({c} : Finset (entropyParty n)) := by
      have hx : entropyLabelA ∈ ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
      rw [← h] at hx; exact hx
    exact hAC (Finset.mem_singleton.mp this)
  have n3 : ({c} : Finset (entropyParty n)) ≠ {entropyLabelA} := by
    intro h
    exact hAC.symm (Finset.singleton_inj.mp h)
  have n4 : ({c} : Finset (entropyParty n)) ≠ {b} ∪ {c} ∪ {entropyLabelA} := by
    intro h
    have : (b : entropyParty n) ∈ ({c} : Finset (entropyParty n)) := by
      have hx : b ∈ ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))))
      rw [← h] at hx; exact hx
    exact hBC (Finset.mem_singleton.mp this)
  simp only [n1, n2, n3, n4, ite_true, ite_false]
  norm_num

theorem AuxForm_IABC_not_mem {n : ℕ} :
    cmiForm ({entropyLabelA} : Finset (entropyParty n)) {b} {c} ∉ constraints n := by
  intro h
  have hval : cmiForm ({entropyLabelA} : Finset (entropyParty n)) {b} {c} {c} = -1 := by
    have hA := (AuxForm_labels_ne (n := n)).1
    have hAC := (AuxForm_labels_ne (n := n)).2.1
    have hBC := (AuxForm_labels_ne (n := n)).2.2
    exact AuxForm_std_at_cond hA hAC hBC
  rw [AuxForm_mem_constraints] at h
  rcases h with h | h
  · have := congrFun h {c}
    simp [hval, AuxForm_IACB_at_C] at this
  · have := congrFun h {c}
    simp [hval, AuxForm_IBCA_at_C] at this

theorem AuxMatch_classify {n p : ℕ} {U V W : Finset (entropyParty n)}
    {alpha : Fin p → Finset (entropyParty n)}
    (h : MatchingInstance (constraints n) U V W alpha) :
    (W = ∅ ∨ (U = ∅ ∧ V = ∅)) ∨
      (W = {c} ∧
        ((U = {entropyLabelA} ∧ V = {b}) ∨
          (U = {b} ∧ V = {entropyLabelA}))) := by
  have hInst := h.1
  have htrip : DisjointTriple U W V := ⟨hInst.1.2.1, hInst.1.1, hInst.1.2.2.symm⟩
  have htrip2 : DisjointTriple V W U := ⟨hInst.1.2.2, hInst.1.1.symm, hInst.1.2.1.symm⟩
  have hA := (AuxForm_labels_ne (n := n)).1
  have hAC := (AuxForm_labels_ne (n := n)).2.1
  have hBC := (AuxForm_labels_ne (n := n)).2.2
  rcases h.2.1 with h1z | h1Z
  · rcases h.2.2 with h2z | h2Z
    · have h1 := (AuxForm_cmi_eq_zero_of_triple htrip).mp h1z
      have h2 := (AuxForm_cmi_eq_zero_of_triple htrip2).mp h2z
      rcases h1 with hU | hW
      · rcases h2 with hV | hW'
        · exact Or.inl (Or.inr ⟨hU, hV⟩)
        · exact Or.inl (Or.inl hW')
      · exact Or.inl (Or.inl hW)
    · have h1 := (AuxForm_cmi_eq_zero_of_triple htrip).mp h1z
      rcases h1 with hU | hW
      · have heq : cmiForm V W U = miForm V W := by
          subst hU; exact AuxForm_cmi_empty_cond V W
        rcases AuxForm_mem_constraints.mp h2Z with hL | hL
        · exact (AuxForm_mi_ne_std hAC hA hBC.symm (heq.symm.trans hL)).elim
        · exact (AuxForm_mi_ne_std hBC hA.symm hAC.symm (heq.symm.trans hL)).elim
      · have h0 : cmiForm V W U = 0 := by
          subst hW; exact AuxForm_cmi_zero_emptyV V U
        rcases AuxForm_mem_constraints.mp h2Z with hL | hL
        · exact (AuxForm_std_ne_zero hAC hA hBC.symm (hL.symm.trans h0)).elim
        · exact (AuxForm_std_ne_zero hBC hA.symm hAC.symm (hL.symm.trans h0)).elim
  · rcases h.2.2 with h2z | h2Z
    · have h2 := (AuxForm_cmi_eq_zero_of_triple htrip2).mp h2z
      rcases h2 with hV | hW
      · have heq : cmiForm U W V = miForm U W := by
          subst hV; exact AuxForm_cmi_empty_cond U W
        rcases AuxForm_mem_constraints.mp h1Z with hL | hL
        · exact (AuxForm_mi_ne_std hAC hA hBC.symm (heq.symm.trans hL)).elim
        · exact (AuxForm_mi_ne_std hBC hA.symm hAC.symm (heq.symm.trans hL)).elim
      · have h0 : cmiForm U W V = 0 := by
          subst hW; exact AuxForm_cmi_zero_emptyV U V
        rcases AuxForm_mem_constraints.mp h1Z with hL | hL
        · exact (AuxForm_std_ne_zero hAC hA hBC.symm (hL.symm.trans h0)).elim
        · exact (AuxForm_std_ne_zero hBC hA.symm hAC.symm (hL.symm.trans h0)).elim
    · rcases AuxForm_mem_constraints.mp h1Z with hL | hL
      · have hc := AuxForm_cmi_eq_std htrip hAC hA hBC.symm hL
        rcases hc with ⟨hV, hUW⟩
        rcases hUW with ⟨hU, hW⟩ | ⟨hU, hW⟩
        · exact Or.inr ⟨hW, Or.inl ⟨hU, hV⟩⟩
        · have h2form : cmiForm V W U =
              cmiForm ({entropyLabelA} : Finset (entropyParty n)) {b} {c} := by
            subst hV; subst hU; subst hW
            exact AuxForm_cmi_symm {b} {entropyLabelA} {c}
          exact (AuxForm_IABC_not_mem (by simpa [h2form] using h2Z)).elim
      · have hc := AuxForm_cmi_eq_std htrip hBC hA.symm hAC.symm hL
        rcases hc with ⟨hV, hUW⟩
        rcases hUW with ⟨hU, hW⟩ | ⟨hU, hW⟩
        · exact Or.inr ⟨hW, Or.inr ⟨hU, hV⟩⟩
        · have h2form : cmiForm V W U =
              cmiForm ({entropyLabelA} : Finset (entropyParty n)) {b} {c} := by
            subst hV; subst hU; subst hW
            -- V={A}, W={B}, U={C}: already I(A:B|C)
            rfl
          exact (AuxForm_IABC_not_mem (by simpa [h2form] using h2Z)).elim

theorem AuxForm_ABC_eq {n : ℕ} :
    ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) =
      {entropyLabelA, b, c} := by
  ext t
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    or_comm, or_left_comm, or_assoc]

theorem AuxForm_BAC_eq {n : ℕ} :
    ({b} ∪ {entropyLabelA} ∪ {c} : Finset (entropyParty n)) =
      {entropyLabelA, b, c} := by
  ext t
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    or_comm, or_left_comm, or_assoc]

theorem AuxWitness_quantum_nonneg (n : ℕ) (hn : 2 ≤ n)
    (L : Form (entropyParty n)) (hL : QuantumBasic L) :
    0 ≤ evaluateEntropyForm L (AuxWitness n) := by
  obtain ⟨U, V, W, hdis, hform⟩ := hL
  rcases hdis with ⟨hUV, hUW, hVW⟩
  rcases hform with hform | hform
  · subst hform
    exact AuxWitness_cmi_nonneg n hn hUV hUW hVW
  · subst hform
    exact AuxWitness_wmo_nonneg n hn hUV hUW hVW

theorem AuxWitness_other_nonneg (n : ℕ) (hn : 2 ≤ n)
    (L : Form (entropyParty n)) (hL : OtherFamily n L) :
    0 ≤ evaluateEntropyForm L (AuxWitness n) := by
  obtain ⟨p, U, V, W, alpha, hp, hpne, hM, rfl⟩ := hL
  have hInst : DisjointInstance U V W alpha := hM.1
  rcases AuxMatch_classify hM with hdeg | hnd
  · exact AuxWitness_family_deg hn hInst hdeg
  · rcases hnd with ⟨hW, hUV⟩
    have hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j) := hInst.2.2
    have hX : ∀ i, AuxSE_isX (alpha i) := by
      intro i
      have d : Disjoint (alpha i) (U ∪ V ∪ W) := hInst.2.1 i
      apply AuxSE_isX_of_disj_ABC
      rcases hUV with ⟨hU, hV⟩ | ⟨hU, hV⟩
      · subst hW; subst hU; subst hV
        rw [AuxForm_ABC_eq] at d
        exact d
      · subst hW; subst hU; subst hV
        rw [AuxForm_BAC_eq] at d
        exact d
    have hev := AuxWitness_family_eq_f hInst
    rcases hUV with ⟨hU, hV⟩ | ⟨hU, hV⟩
    · subst hW; subst hU; subst hV
      rw [hev]
      exact AuxSE_family_nonneg n p hn hp hpne hX hdisj
    · subst hW; subst hU; subst hV
      rw [hev, AuxForm_family_symm]
      exact AuxSE_family_nonneg n p hn hp hpne hX hdisj

theorem AuxWitness_constraints (n : ℕ) :
    ∀ Z ∈ constraints n, evaluateEntropyForm Z (AuxWitness n) = 0 := by
  intro Z hZ
  rw [AuxForm_mem_constraints] at hZ
  rcases hZ with hZ | hZ
  · subst hZ; exact AuxWitness_constr_AC n
  · subst hZ; exact AuxWitness_constr_BC n

theorem AuxSE_standard_inst (n : ℕ) :
    DisjointInstance ({entropyLabelA} : Finset (entropyParty n)) {b} {c} standardX := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [entropyLabelA, b]
  · simp [entropyLabelA, c]
  · simp [b, c]
  · intro i
    simp [standardX, x, entropyLabelA, b, c]
  · intro i j hij
    exact AuxSE_disj_standard hij

theorem AuxWitness_standard_eval (n : ℕ) :
    evaluateEntropyForm (standardFamily n) (AuxWitness n) =
      evaluateEntropyForm (standardFamily n) (separatingF n) := by
  simpa [standardFamily] using
    AuxWitness_family_eq_f (AuxSE_standard_inst n)

theorem AuxWitness_standard_neg (n : ℕ) (hn : 2 ≤ n) :
    evaluateEntropyForm (standardFamily n) (AuxWitness n) < 0 := by
  rw [AuxWitness_standard_eval, AuxSE_standard_eval]
  have hn0 : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn)
  nlinarith

theorem AuxWitness_not_derivable (n : ℕ) (hn : 2 ≤ n) :
    ¬ Derivable {L | QuantumBasic L ∨ OtherFamily n L}
      (constraints n) (standardFamily n) := by
  rintro ⟨k, L, w, r, hAll, hnn, heq⟩
  have hev :
      evaluateEntropyForm (standardFamily n) (AuxWitness n) =
        (∑ i, w i * evaluateEntropyForm (L i) (AuxWitness n)) +
          ∑ z : constraints n, r z * evaluateEntropyForm z.1 (AuxWitness n) := by
    rw [heq, AuxSE_ev_add, AuxSE_ev_sum_smul, AuxSE_ev_sum_smul]
  have hz : ∀ z : constraints n, evaluateEntropyForm z.1 (AuxWitness n) = 0 := by
    intro z
    exact AuxWitness_constraints n z.1 z.2
  simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at hev
  have hnn' : 0 ≤ ∑ i, w i * evaluateEntropyForm (L i) (AuxWitness n) := by
    apply Finset.sum_nonneg
    intro i _
    refine mul_nonneg (hnn i) ?_
    have hi := hAll i
    simp only [Set.mem_ofPred_eq] at hi
    rcases hi with hB | hN
    · exact AuxWitness_quantum_nonneg n hn (L i) hB
    · exact AuxWitness_other_nonneg n hn (L i) hN
  have hneg : evaluateEntropyForm (standardFamily n) (AuxWitness n) < 0 :=
    AuxWitness_standard_neg n hn
  linarith

theorem quantumFamily_independent (n : ℕ) (hn : 2 ≤ n) :
    ¬ Derivable {L | QuantumBasic L ∨ OtherFamily n L}
      (constraints n) (standardFamily n) :=
  AuxWitness_not_derivable n hn

theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    ¬ Derivable {L | QuantumBasic L ∨ OtherFamily n L}
      (constraints n) (standardFamily n) :=
  quantumFamily_independent n hn


end QAlgorithms.Papers.Independent.Intake100.P66

end
