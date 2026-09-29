-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_interp_reflection_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:47:35.613711+00:00
-- url     : https://prove2.me/submissions/59c508f4-0a35-465d-8576-186e543f5536

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_braidInterp_reflection_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_reflection_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_left_braid_reflection_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightOuterInterpFun_reflect_a_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ) :
    rightOuterInterpFun n i j u q (strandIdx i) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        leftOuterInterpFun n i j u q (strandIdxSucc j)) := by
  have hR := thm_3_15_adjacent_right_left_braid_reflection_v1 i j hji
  have hO := thm_3_15_adjacent_outer_reflection_v1 i j hji
  unfold rightOuterInterpFun leftOuterInterpFun
  calc
    braidInterp u (rightBraidFun n i j q (strandIdx i))
        (outerRotateFun n i q (strandIdx i)) =
      braidInterp u
        ((((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
          leftBraidFun n i j q (strandIdxSucc j)))
        ((((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
          outerRotateFun n i q (strandIdxSucc j))) := by
            exact congrArg₂ (braidInterp u) (hR.1 q) (hO.1 q)
    _ = (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        braidInterp u (leftBraidFun n i j q (strandIdxSucc j))
          (outerRotateFun n i q (strandIdxSucc j))) := by
            exact thm_3_15_adjacent_braidInterp_reflection_v1
              u (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ))
                (leftBraidFun n i j q (strandIdxSucc j))
                (outerRotateFun n i q (strandIdxSucc j))

lemma rightOuterInterpFun_reflect_b_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ) :
    rightOuterInterpFun n i j u q (strandIdxSucc i) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        leftOuterInterpFun n i j u q (strandIdxSucc i)) := by
  have hR := thm_3_15_adjacent_right_left_braid_reflection_v1 i j hji
  have hO := thm_3_15_adjacent_outer_reflection_v1 i j hji
  unfold rightOuterInterpFun leftOuterInterpFun
  calc
    braidInterp u (rightBraidFun n i j q (strandIdxSucc i))
        (outerRotateFun n i q (strandIdxSucc i)) =
      braidInterp u
        ((((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
          leftBraidFun n i j q (strandIdxSucc i)))
        ((((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
          outerRotateFun n i q (strandIdxSucc i))) := by
            exact congrArg₂ (braidInterp u) (hR.2.1 q) (hO.2.1 q)
    _ = (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        braidInterp u (leftBraidFun n i j q (strandIdxSucc i))
          (outerRotateFun n i q (strandIdxSucc i))) := by
            exact thm_3_15_adjacent_braidInterp_reflection_v1
              u (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ))
                (leftBraidFun n i j q (strandIdxSucc i))
                (outerRotateFun n i q (strandIdxSucc i))

lemma rightOuterInterpFun_reflect_c_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ) :
    rightOuterInterpFun n i j u q (strandIdxSucc j) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        leftOuterInterpFun n i j u q (strandIdx i)) := by
  have hR := thm_3_15_adjacent_right_left_braid_reflection_v1 i j hji
  have hO := thm_3_15_adjacent_outer_reflection_v1 i j hji
  unfold rightOuterInterpFun leftOuterInterpFun
  calc
    braidInterp u (rightBraidFun n i j q (strandIdxSucc j))
        (outerRotateFun n i q (strandIdxSucc j)) =
      braidInterp u
        ((((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
          leftBraidFun n i j q (strandIdx i)))
        ((((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
          outerRotateFun n i q (strandIdx i))) := by
            exact congrArg₂ (braidInterp u) (hR.2.2 q) (hO.2.2 q)
    _ = (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        braidInterp u (leftBraidFun n i j q (strandIdx i))
          (outerRotateFun n i q (strandIdx i))) := by
            exact thm_3_15_adjacent_braidInterp_reflection_v1
              u (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ))
                (leftBraidFun n i j q (strandIdx i))
                (outerRotateFun n i q (strandIdx i))

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ),
        rightOuterInterpFun n i j u q (strandIdx i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftOuterInterpFun n i j u q (strandIdxSucc j))) ∧
      (∀ (u q : ℝ),
        rightOuterInterpFun n i j u q (strandIdxSucc i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftOuterInterpFun n i j u q (strandIdxSucc i))) ∧
      (∀ (u q : ℝ),
        rightOuterInterpFun n i j u q (strandIdxSucc j) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftOuterInterpFun n i j u q (strandIdx i))) := by
  intro n i j hji
  exact ⟨rightOuterInterpFun_reflect_a_v1 i j hji,
    ⟨rightOuterInterpFun_reflect_b_v1 i j hji,
      rightOuterInterpFun_reflect_c_v1 i j hji⟩⟩
