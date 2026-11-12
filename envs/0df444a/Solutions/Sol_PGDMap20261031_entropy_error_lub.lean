-- Prove2me | solution 1 for PGDMap20261031.entropy_error_lub
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:44:07.911886+00:00
-- url     : https://prove2.me/submissions/97b99588-b796-427f-92e7-ef285b9b3281

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031
open scoped BigOperators

theorem solution : ErrorProfileLUBClaim := by
  intro M c p hvalid
  have hp : 0 < p := hvalid.2.2
  have hAbar : 0 ≤ curvatureAtBoundary M := by
    unfold curvatureAtBoundary
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (mul_nonneg (le_of_lt (M.weight_pos j)) (le_of_lt (M.a_pos j)))
      (by linarith [M.a_lt_one j])
  let C := 1 + curvatureAtBoundary M / M.lambda
  have hC : 1 ≤ C := by
    have := div_nonneg hAbar (le_of_lt M.lambda_pos)
    dsimp [C]
    linarith
  have hClambda : curvatureAtBoundary M ≤ C * M.lambda := by
    dsimp [C]
    field_simp [ne_of_gt M.lambda_pos]
    nlinarith [M.lambda_pos]
  apply isLUB_csSup
  · exact ⟨|curvatureError M c p 0|, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  · refine ⟨C, ?_⟩
    rintro v ⟨t, ht, rfl⟩
    have htden : 0 < 1 - t ^ 2 := by
      nlinarith [ht.1, ht.2]
    have hA : 0 ≤ mixtureCurvature M t := by
      unfold mixtureCurvature
      apply Finset.sum_nonneg
      intro j _
      apply div_nonneg (mul_nonneg (le_of_lt (M.weight_pos j)) (le_of_lt (M.a_pos j)))
      nlinarith [M.a_pos j, M.a_lt_one j]
    have hAle : mixtureCurvature M t ≤ curvatureAtBoundary M := by
      unfold mixtureCurvature curvatureAtBoundary
      apply Finset.sum_le_sum
      intro j _
      have ha : 0 < 1 - M.a j := by linarith [M.a_lt_one j]
      have hat : 0 < 1 - M.a j * t ^ 2 := by
        nlinarith [M.a_pos j, M.a_lt_one j]
      apply (div_le_div_iff₀ hat ha).2
      exact mul_le_mul_of_nonneg_left (by nlinarith [M.a_pos j])
        (mul_nonneg (le_of_lt (M.weight_pos j)) (le_of_lt (M.a_pos j)))
    have hB : M.lambda ≤ entropyCurvature M t := by
      unfold entropyCurvature
      apply (le_div_iff₀ htden).2
      nlinarith [sq_nonneg t, M.lambda_pos]
    have hk : 0 < powerCurvature c t := by
      unfold powerCurvature
      exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
        (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)
    have hv : 0 < p * powerCurvature c t := mul_pos hp hk
    have hd : 0 < p * powerCurvature c t + entropyCurvature M t := by
      linarith [M.lambda_pos]
    have hCd : p * powerCurvature c t + entropyCurvature M t ≤
        C * (p * powerCurvature c t + entropyCurvature M t) := by nlinarith
    have hCl : C * M.lambda ≤
        C * (p * powerCurvature c t + entropyCurvature M t) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    unfold curvatureError
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hd).2
      nlinarith
    · apply (div_le_iff₀ hd).2
      linarith [M.lambda_pos]
