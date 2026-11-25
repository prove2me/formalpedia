-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_gram_eq_801d9bae3823
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:45:51.139811+00:00
-- url     : https://prove2.me/submissions/7a4e8423-6e01-423a-8883-e21f77732c10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_signatureForm_eq_453eabc89093
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
variable {N : ℕ}
variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
    topPoly' i hi L * (sigTop p i hi).map C * topPoly i hi L +
      (X ^ 2 : ℂ[X]) • (tailForm p i hi L).map C := by
  rw [signatureForm_eq]
  refine Matrix.ext fun a b => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply]
  simp only [Matrix.diagonal_map (map_zero C), Matrix.mul_diagonal]
  rw [sum_fin_split_castLE hi]
  congr 1
  · rw [sigTop, Matrix.diagonal_map (map_zero C), Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rfl
  · simp only [tailForm, Matrix.of_apply, map_sum, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · have h1 : ∀ a : Fin i, c ≠ Fin.castLE hi a := fun a h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp only [rowPoly, colPoly, Matrix.of_apply, h1, if_false, zero_add, map_mul]
      ring
    · simp
end GroundTheory.Heights₂.Heights.FourB
