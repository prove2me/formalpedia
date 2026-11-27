-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_proof_e79f7e0fcefc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:34.948049+00:00
-- url     : https://prove2.me/submissions/de28d5a0-8727-4113-86b1-81a596f02831

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PHermitianDetMono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_one_le_det_one_add_bb3f4c9f8b7a
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
open Matrix
open scoped ComplexOrder MatrixOrder
namespace GroundTheory.Heights₂.Heights.FourB
namespace HermitianDetMono
theorem _root_.solution : HermitianDetMono.Statement := by
  intro n A B hB hAB
  have hA : A.PosSemidef := by simpa using hB.add hAB
  suffices h : B.det ≤ A.det from (Complex.le_def.mp h).1
  by_cases hdet : B.det = 0
  · rw [hdet]; exact hA.det_nonneg
  · obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    have hy : IsUnit y.det := by
      rw [det_mul] at hdet
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
    set M := (y⁻¹)ᴴ * (A - star y * y) * y⁻¹ with hMdef
    have hM : M.PosSemidef := hAB.conjTranspose_mul_mul_same y⁻¹
    have hfac : A = star y * (1 + M) * y := by
      have h1 : star y * (y⁻¹)ᴴ = 1 := by
        rw [star_eq_conjTranspose, ← conjTranspose_mul, nonsing_inv_mul y hy, conjTranspose_one]
      rw [hMdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
        nonsing_inv_mul y hy, Matrix.mul_one]
      abel
    have hdA : A.det = (1 + M).det * (star y * y).det := by
      conv_lhs => rw [hfac]
      rw [det_mul, det_mul, det_mul]; ring
    rw [hdA]
    exact le_mul_of_one_le_left hB.det_nonneg (HermitianDetMono.one_le_det_one_add hM)
end HermitianDetMono
end GroundTheory.Heights₂.Heights.FourB
