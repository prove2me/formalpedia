-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_M__mul_R__sub_one_c7dee40b7706
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:47.361827+00:00
-- url     : https://prove2.me/submissions/4fd65796-2de6-4984-a5c7-134a1f3933be

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
section
namespace GroupTheoreticShannonCapacity.MAlpha
open Matrix
section DetLemmas
end DetLemmas
private lemma Mα_mul_Rα_sub_one_diag (m : ℕ) (α : ℝ) (i : Fin (m + 1)) :
    ∑ x : Fin (m + 1),
      (if (i : ℕ) < (x : ℕ) then α else if (i : ℕ) > (x : ℕ) then -1 else 0) *
        ((if (x : ℕ) = 0 ∧ (i : ℕ) = m then -α else if (x : ℕ) = (i : ℕ) + 1 then 1 else 0) -
          if x = i then 1 else 0) =
    (if (i : ℕ) = 0 ∧ (i : ℕ) = m then -α else 0) + α := by
  -- Case split on m = 0 vs m > 0
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- Case m = 0: n = 1, only term is x = i = 0, and M_α(0,0) = 0
    subst hm0
    have hi0 : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi0
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, lt_irrefl, ite_false, and_self, ite_true, zero_mul, neg_add_cancel]
  · -- Case m > 0
    by_cases hi_eq_m : (i : ℕ) = m
    · -- Subcase i = m: corner term x = 0 contributes
      have hi_ne_0 : (i : ℕ) ≠ 0 := by omega
      have h_not_corner_lhs : ¬((i : ℕ) = 0 ∧ (i : ℕ) = m) := by omega
      simp only [h_not_corner_lhs, ite_false, zero_add]
      rw [Finset.sum_eq_single 0]
      · -- Main term x = 0: M_α(m, 0) = -1, R_α(0, m) = -α
        simp only [Fin.val_zero, hi_eq_m, and_self, ite_true]
        have h0_ne_i : (0 : Fin (m + 1)) ≠ i := by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
        simp only [h0_ne_i, ite_false, sub_zero]
        have hm_not_lt_0 : ¬(m < (0 : ℕ)) := Nat.not_lt_zero m
        simp only [hm_not_lt_0, ite_false, hm_pos, ite_true, neg_one_mul, neg_neg]
      · -- Other terms x ≠ 0
        intro x _ hx0
        have hx_ne_0 : (x : ℕ) ≠ 0 := fun h => hx0 (Fin.ext h)
        have h_not_corner : ¬((x : ℕ) = 0 ∧ (i : ℕ) = m) := by omega
        by_cases hx_eq_i1 : (x : ℕ) = (i : ℕ) + 1
        · -- x = i + 1 = m + 1 but x < m + 1, contradiction
          have : (x : ℕ) < m + 1 := x.isLt; omega
        · -- x ≠ 0 and x ≠ i + 1
          by_cases hx_eq_i : x = i
          · subst hx_eq_i; simp only [lt_irrefl, ite_false, zero_mul]
          · have hx_ne_i : (x : ℕ) ≠ (i : ℕ) := fun h => hx_eq_i (Fin.ext h)
            simp only [h_not_corner, ite_false, hx_eq_i1, hx_eq_i, sub_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- Subcase i < m: term x = i + 1 contributes
      have hi_lt_m : (i : ℕ) < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi_eq_m
      have h_not_corner_lhs : ¬((i : ℕ) = 0 ∧ (i : ℕ) = m) := by omega
      simp only [h_not_corner_lhs, ite_false, zero_add]
      -- The contributing term is x = ⟨i + 1, ...⟩
      let i1 : Fin (m + 1) := ⟨(i : ℕ) + 1, Nat.add_lt_add_right hi_lt_m 1⟩
      rw [Finset.sum_eq_single i1]
      · -- Main term x = i + 1: M_α(i, i+1) = α, R_α(i+1, i) = 1
        simp only [i1]
        have hi_lt_i1 : (i : ℕ) < (i : ℕ) + 1 := Nat.lt_succ_self _
        have h_not_corner : ¬(((i : ℕ) + 1) = 0 ∧ (i : ℕ) = m) := by omega
        have hi1_lt : (i : ℕ) + 1 < m + 1 := Nat.add_lt_add_right hi_lt_m 1
        have hi1_ne_i : ¬(⟨(i : ℕ) + 1, hi1_lt⟩ : Fin (m + 1)) = i := by
          simp only [Fin.ext_iff]; omega
        simp only [h_not_corner, ite_false, ite_true, hi1_ne_i, sub_zero, hi_lt_i1, mul_one]
      · -- Other terms x ≠ i + 1
        intro x _ hx_ne_i1
        have hx_ne_i1' : (x : ℕ) ≠ (i : ℕ) + 1 := fun h => hx_ne_i1 (Fin.ext h)
        by_cases hx_eq_i : x = i
        · subst hx_eq_i; simp only [lt_irrefl, ite_false, zero_mul]
        · have hx_ne_i : (x : ℕ) ≠ (i : ℕ) := fun h => hx_eq_i (Fin.ext h)
          by_cases hx0_im : (x : ℕ) = 0 ∧ (i : ℕ) = m
          · omega  -- contradicts hi_lt_m
          · simp only [hx0_im, ite_false, hx_ne_i1', hx_eq_i, sub_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
private lemma Mα_mul_Rα_sub_one_subdiag (m : ℕ) (α : ℝ) (i j : Fin (m + 1))
    (hij : i ≠ j) (hij1 : (i : ℕ) = (j : ℕ) + 1) :
    ∑ x : Fin (m + 1),
      (if (i : ℕ) < (x : ℕ) then α else if (i : ℕ) > (x : ℕ) then -1 else 0) *
        ((if (x : ℕ) = 0 ∧ (j : ℕ) = m then -α else if (x : ℕ) = (j : ℕ) + 1 then 1 else 0) -
          if x = j then 1 else 0) = 1 := by
  -- Only the term x = j contributes: M_α(i,j) * (R_α(j,j) - 1) = (-1) * (-1) = 1
  rw [Finset.sum_eq_single j]
  · -- Main term: x = j
    have hj_lt_i : (j : ℕ) < (i : ℕ) := by omega
    simp only [hj_lt_i.asymm, ite_false, hj_lt_i, ite_true]
    -- Corner condition: j ≠ 0 ∨ j ≠ m (since i = j+1 ≤ m implies j < m, unless m = 0 and j = 0)
    have hj_ne_corner : ¬((j : ℕ) = 0 ∧ (j : ℕ) = m) := by
      intro ⟨hj0, hjm⟩
      have : m = 0 := by omega
      have hi1 : (i : ℕ) = 1 := by omega
      have him : (i : ℕ) < m + 1 := i.isLt
      omega
    have hj_ne_j1 : (j : ℕ) ≠ (j : ℕ) + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
    simp only [hj_ne_corner, ite_false, hj_ne_j1]
    ring
  · -- Other terms x ≠ j are zero
    intro x _ hxj
    have hx_ne_j : (x : ℕ) ≠ (j : ℕ) := fun h => hxj (Fin.ext h)
    by_cases hx_eq_j1 : (x : ℕ) = (j : ℕ) + 1
    · -- x = j + 1 = i, so M_α(i, i) = 0
      have hx_eq_i : x = i := Fin.ext (by omega)
      subst hx_eq_i; simp only [lt_irrefl, ite_false, zero_mul]
    · -- x ≠ j and x ≠ j + 1
      by_cases hx0m : (x : ℕ) = 0 ∧ (j : ℕ) = m
      · -- x = 0, j = m, so i = m + 1, but i < m + 1, contradiction
        omega
      · simp only [hx0m, ite_false, hx_eq_j1, hxj, sub_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
private lemma Mα_mul_Rα_sub_one_corner (m : ℕ) (α : ℝ) (i j : Fin (m + 1))
    (hij : i ≠ j) (hi0 : (i : ℕ) = 0) (hjm : (j : ℕ) = m) :
    ∑ x : Fin (m + 1),
      (if (i : ℕ) < (x : ℕ) then α else if (i : ℕ) > (x : ℕ) then -1 else 0) *
        ((if (x : ℕ) = 0 ∧ (j : ℕ) = m then -α else if (x : ℕ) = (j : ℕ) + 1 then 1 else 0) -
          if x = j then 1 else 0) = -α := by
  -- The only contributing term is x = j = m
  -- M_α(0, m) = α (since 0 < m), R_α(m, m) = 0, δ(m, j) = 1
  -- Contribution: α * (0 - 1) = -α
  have hm_pos : 0 < m := by
    by_contra h
    push_neg at h
    have hm0 : m = 0 := Nat.le_zero.mp h
    have hieqj : (i : ℕ) = (j : ℕ) := by omega
    exact hij (Fin.ext hieqj)
  rw [Finset.sum_eq_single j]
  · -- Main term x = j: M_α(0, m) = α, R_α(m, m) = 0, δ(m, m) = 1
    simp only [hi0, hjm]
    have h0_lt_m : (0 : ℕ) < m := hm_pos
    have h_m_ne_0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
    have h_not_subdiag : (m : ℕ) ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
    simp only [h0_lt_m, ite_true, h_m_ne_0, false_and, ite_false, h_not_subdiag]
    ring
  · -- Other terms x ≠ j
    intro x _ hxj
    have hx_ne_j : (x : ℕ) ≠ (j : ℕ) := fun h => hxj (Fin.ext h)
    simp only [hi0, hjm]
    by_cases hx0 : (x : ℕ) = 0
    · -- x = 0: M_α(0, 0) = 0
      simp only [hx0, lt_irrefl, ite_false, zero_mul]
    · -- x ≠ 0
      have h0_lt_x : (0 : ℕ) < (x : ℕ) := Nat.pos_of_ne_zero hx0
      simp only [h0_lt_x, ite_true]
      have h_not_corner : ¬((x : ℕ) = 0 ∧ m = m) := by omega
      by_cases hx_eq_j1 : (x : ℕ) = m + 1
      · -- x = m + 1 but x < m + 1, contradiction
        have : (x : ℕ) < m + 1 := x.isLt; omega
      · simp only [hx0, false_and, ite_false, hx_eq_j1, hxj, sub_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
private lemma Mα_mul_Rα_sub_one_other (m : ℕ) (α : ℝ) (i j : Fin (m + 1))
    (hij : i ≠ j) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) (hcorner : ¬((i : ℕ) = 0 ∧ (j : ℕ) = m)) :
    ∑ x : Fin (m + 1),
      (if (i : ℕ) < (x : ℕ) then α else if (i : ℕ) > (x : ℕ) then -1 else 0) *
        ((if (x : ℕ) = 0 ∧ (j : ℕ) = m then -α else if (x : ℕ) = (j : ℕ) + 1 then 1 else 0) -
          if x = j then 1 else 0) = 0 := by
  -- Split into cases: j < m vs j = m
  by_cases hjm : (j : ℕ) = m
  · -- Case j = m: corner term x = 0 and x = j = m contribute and cancel
    -- hcorner implies i ≠ 0, so i > 0
    have hi_ne_0 : (i : ℕ) ≠ 0 := fun h => hcorner ⟨h, hjm⟩
    have hi_pos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi_ne_0
    have hi_ne_j : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hi_lt_m : (i : ℕ) < m := by have := i.isLt; omega
    have hj_ne_0 : (j : ℕ) ≠ 0 := by omega
    have h0_ne_j : (0 : Fin (m + 1)) ≠ j := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
    -- We extract 0 from the sum, then j from what remains
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ← Finset.sdiff_singleton_eq_erase]
    conv_lhs => rhs; rw [← Finset.add_sum_erase _ _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, Finset.notMem_singleton.mpr h0_ne_j.symm⟩), ← Finset.sdiff_singleton_eq_erase]
    -- Compute term at x = 0
    have term0 : (if (i : ℕ) < (0 : Fin (m + 1)).val then α
                  else if (i : ℕ) > (0 : Fin (m + 1)).val then -1 else 0) *
        ((if (0 : Fin (m + 1)).val = 0 ∧ (j : ℕ) = m then -α
          else if (0 : Fin (m + 1)).val = (j : ℕ) + 1 then 1 else 0) -
          if (0 : Fin (m + 1)) = j then 1 else 0) = α := by
      simp only [Fin.val_zero, hjm, and_self, ite_true, h0_ne_j, ite_false, sub_zero,
                 hi_pos.asymm, hi_pos, neg_one_mul, neg_neg]
    -- Compute term at x = j
    have termj : (if (i : ℕ) < (j : ℕ) then α else if (i : ℕ) > (j : ℕ) then -1 else 0) *
        ((if (j : ℕ) = 0 ∧ (j : ℕ) = m then -α
          else if (j : ℕ) = (j : ℕ) + 1 then 1 else 0) -
          if j = j then 1 else 0) = -α := by
      simp only [ite_true]
      have hj_ne_j1 : (j : ℕ) ≠ (j : ℕ) + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
      have hi_lt_j : (i : ℕ) < (j : ℕ) := by omega
      simp only [hj_ne_0, false_and, ite_false, hj_ne_j1, hi_lt_j, ite_true]
      ring
    -- Rest of sum is 0
    have rest_zero : ∑ x ∈ (Finset.univ \ {0}) \ {j},
        (if (i : ℕ) < (x : ℕ) then α else if (i : ℕ) > (x : ℕ) then -1 else 0) *
          ((if (x : ℕ) = 0 ∧ (j : ℕ) = m then -α else if (x : ℕ) = (j : ℕ) + 1 then 1 else 0) -
            if x = j then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hx
      have hx_ne_0 : (x : ℕ) ≠ 0 := fun h => hx.1 (Fin.ext h)
      have hx_ne_j : (x : ℕ) ≠ (j : ℕ) := fun h => hx.2 (Fin.ext h)
      have h_not_corner : ¬((x : ℕ) = 0 ∧ (j : ℕ) = m) := by omega
      by_cases hx_eq_j1 : (x : ℕ) = (j : ℕ) + 1
      · have : (x : ℕ) < m + 1 := x.isLt; omega
      · by_cases hx_eq_i : x = i
        · simp only [hx_eq_i, lt_irrefl, ite_false, zero_mul]
        · have hxj : ¬(x = j) := hx.2
          simp only [h_not_corner, hx_eq_j1, ite_false, if_neg hxj, sub_zero, mul_zero]
    rw [rest_zero, add_zero, term0, termj]
    ring
  · -- Case j < m: terms x = j and x = j+1 contribute and cancel
    have hj_lt_m : (j : ℕ) < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hjm
    let j1 : Fin (m + 1) := ⟨(j : ℕ) + 1, Nat.add_lt_add_right hj_lt_m 1⟩
    have hj1_ne_j : j1 ≠ j := by simp only [j1, ne_eq, Fin.ext_iff]; omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.sdiff_singleton_eq_erase]
    rw [← Finset.add_sum_erase _ _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
         Finset.notMem_singleton.mpr hj1_ne_j⟩), ← Finset.sdiff_singleton_eq_erase]
    -- Compute term at x = j
    have termj : (if (i : ℕ) < (j : ℕ) then α else if (i : ℕ) > (j : ℕ) then -1 else 0) *
        ((if (j : ℕ) = 0 ∧ (j : ℕ) = m then -α
          else if (j : ℕ) = (j : ℕ) + 1 then 1 else 0) -
          if j = j then 1 else 0) =
        -(if (i : ℕ) < (j : ℕ) then α else if (i : ℕ) > (j : ℕ) then -1 else 0) := by
      simp only [ite_true]
      have hj_ne_j1 : (j : ℕ) ≠ (j : ℕ) + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
      have h_not_corner_j : ¬((j : ℕ) = 0 ∧ (j : ℕ) = m) := by omega
      simp only [h_not_corner_j, ite_false, hj_ne_j1]
      ring
    -- Compute term at x = j + 1
    have termj1 : (if (i : ℕ) < (j1 : ℕ) then α else if (i : ℕ) > (j1 : ℕ) then -1 else 0) *
        ((if (j1 : ℕ) = 0 ∧ (j : ℕ) = m then -α
          else if (j1 : ℕ) = (j : ℕ) + 1 then 1 else 0) -
          if j1 = j then 1 else 0) =
        (if (i : ℕ) < (j : ℕ) then α else if (i : ℕ) > (j : ℕ) then -1 else 0) := by
      simp only [j1]
      have hj1_ne_0 : (j : ℕ) + 1 ≠ 0 := by omega
      have h_not_corner_j1 : ¬((j : ℕ) + 1 = 0 ∧ (j : ℕ) = m) := by omega
      have hj1_ne_j' : ¬(⟨(j : ℕ) + 1, Nat.add_lt_add_right hj_lt_m 1⟩ : Fin (m + 1)) = j := by
        simp only [Fin.ext_iff]; omega
      simp only [h_not_corner_j1, ite_false, ite_true, hj1_ne_j', sub_zero, mul_one]
      -- Show M_α(i, j+1) = M_α(i, j), both have same sign since i ≠ j and i ≠ j+1
      have hi_ne_j : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      by_cases hi_lt_j : (i : ℕ) < (j : ℕ)
      · have hi_lt_j1 : (i : ℕ) < (j : ℕ) + 1 := Nat.lt_succ_of_lt hi_lt_j
        simp only [hi_lt_j, ite_true, hi_lt_j1]
      · have hi_gt_j : (i : ℕ) > (j : ℕ) := Nat.lt_of_le_of_ne (Nat.not_lt.mp hi_lt_j) hi_ne_j.symm
        have hi_gt_j1 : (i : ℕ) > (j : ℕ) + 1 := by omega
        simp only [hi_lt_j, ite_false, hi_gt_j, ite_true, hi_gt_j1.asymm, hi_gt_j1]
    -- Rest of sum is 0
    have rest_zero : ∑ x ∈ (Finset.univ \ {j}) \ {j1},
        (if (i : ℕ) < (x : ℕ) then α else if (i : ℕ) > (x : ℕ) then -1 else 0) *
          ((if (x : ℕ) = 0 ∧ (j : ℕ) = m then -α else if (x : ℕ) = (j : ℕ) + 1 then 1 else 0) -
            if x = j then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hx
      have hx_ne_j : (x : ℕ) ≠ (j : ℕ) := fun h => hx.1 (Fin.ext h)
      have hx_ne_j1 : (x : ℕ) ≠ (j : ℕ) + 1 := fun h => hx.2 (Fin.ext (by simp [j1, h]))
      by_cases hx0m : (x : ℕ) = 0 ∧ (j : ℕ) = m
      · omega  -- contradicts hj_lt_m
      · by_cases hx_eq_i : x = i
        · simp only [hx_eq_i, lt_irrefl, ite_false, zero_mul]
        · have hxj : ¬(x = j) := hx.1
          simp only [hx0m, hx_ne_j1, ite_false, if_neg hxj, sub_zero, mul_zero]
    rw [rest_zero, add_zero, termj, termj1]
    ring
section DetLemmas2
end DetLemmas2
section ConjugationLemmas
end ConjugationLemmas
section Tests
example : ∀ x y α : ℝ, (x • Rα 2 α + y • 1).det = (-x)^2 * α + y^2 := by
  intro x y α
  simp only [Rα, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply,
             Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  -- The matrix entries simplify: (0,0)=y, (0,1)=-xα, (1,0)=x, (1,1)=y
  -- det = y*y - (-xα)*x = y² + x²α
  norm_num [Fin.isValue]
  ring
example : Rα 2 (1 : ℝ) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rα, Matrix.of_apply]
end Tests
end GroupTheoreticShannonCapacity.MAlpha
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (α : ℝ) :
    Mα n α * (Rα n α - 1) = Rα n α + α • 1 := by
  ext i j
  simp only [Matrix.mul_apply, Mα, Rα, Matrix.of_apply, Matrix.sub_apply,
             Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  cases n with
  | zero => exact i.elim0
  | succ m =>
    simp only [Nat.add_sub_cancel]
    -- Use the helper lemmas for each case
    by_cases hij : i = j
    · -- Diagonal case
      subst hij
      simp only [ite_true, mul_one]
      have h1 : ¬((i : ℕ) = (i : ℕ) + 1) := Nat.ne_of_lt (Nat.lt_succ_self _)
      simp only [h1, ite_false]
      exact Mα_mul_Rα_sub_one_diag m α i
    · -- Off-diagonal cases
      have hij' : i ≠ j := hij
      simp only [hij, if_false, mul_zero, add_zero]
      by_cases hij1 : (i : ℕ) = (j : ℕ) + 1
      · -- Subdiagonal
        have hcorner : ¬((i : ℕ) = 0 ∧ (j : ℕ) = m) := by omega
        simp only [hij1, ite_true]
        convert Mα_mul_Rα_sub_one_subdiag m α i j hij' hij1 using 2; simp [hij1]; try (split_ifs <;> first | rfl | omega)
      · -- Not subdiagonal
        by_cases hcorner : (i : ℕ) = 0 ∧ (j : ℕ) = m
        · -- Corner
          have hi0 := hcorner.1
          have hjm := hcorner.2
          simp only [hcorner, and_self, ite_true]
          convert Mα_mul_Rα_sub_one_corner m α i j hij' hi0 hjm using 2; simp only [hi0, hjm]
        · -- Other
          simp only [hij1, hcorner, ite_false]
          exact Mα_mul_Rα_sub_one_other m α i j hij' hij1 hcorner
end GroupTheoreticShannonCapacity.MAlpha
