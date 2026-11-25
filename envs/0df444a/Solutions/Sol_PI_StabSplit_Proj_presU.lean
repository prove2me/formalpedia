-- Prove2me | solution 1 for PI.StabSplit.Proj.presU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:10.358357+00:00
-- url     : https://prove2.me/submissions/17d61d4e-8a8c-4284-9895-0b20a68ac7cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Theorems.Thm_PI_StabSplit_Proj_L_one_sub
import Theorems.Thm_PI_StabSplit_Proj_prj_mul_of_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabSplit PI.StabSplit.Proj
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)
namespace PI.StabSplit.Proj
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (hg : gᴴ * H * g = H)
    (hdet : IsUnit g.det) (C : Matrix ι ι ℂ) (hC : g⁻¹ * Y = Y * C) :
    prj H Y * g * (1 - prj H Y) = 0 := by
  have hgs : IsUnit gᴴ.det := by rw [det_conjTranspose]; exact hdet.star
  have hHg : H * g = (g⁻¹)ᴴ * H := by
    rw [conjTranspose_nonsing_inv]
    calc H * g = (gᴴ)⁻¹ * (gᴴ * H * g) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hgs, Matrix.one_mul]
      _ = (gᴴ)⁻¹ * H := by rw [hg]
  have hL : (Yᴴ * H) * g = Cᴴ * (Yᴴ * H) := by
    rw [Matrix.mul_assoc, hHg, ← Matrix.mul_assoc, ← conjTranspose_mul, hC, conjTranspose_mul,
      Matrix.mul_assoc]
  have : (Yᴴ * H) * (g * (1 - prj H Y)) = 0 := by
    rw [← Matrix.mul_assoc, hL, Matrix.mul_assoc, L_one_sub H Y hG, Matrix.mul_zero]
  rw [Matrix.mul_assoc, prj_mul_of_L H Y _ this]
end PI.StabSplit.Proj
