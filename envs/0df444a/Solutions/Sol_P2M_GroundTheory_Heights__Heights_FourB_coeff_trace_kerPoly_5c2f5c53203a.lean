-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_coeff_trace_kerPoly_5c2f5c53203a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:15.940564+00:00
-- url     : https://prove2.me/submissions/e328dd47-f8e9-41a4-9e1d-34d171a7f746

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
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
variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (L : Matrix (Fin N) (Fin N) ℂ) :
    (kerPoly p i hi L).trace.coeff 0 = (sigTop p i hi * tailForm p i hi L).trace := by
  have hV : (topPoly i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly, colPoly, Matrix.one_apply, Fin.castLE_inj] <;> split_ifs <;> simp
  have hV' : (topPoly' i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly', rowPoly, Matrix.one_apply, Fin.castLE_inj, eq_comm] <;> split_ifs <;> simp
  have hadj : ∀ M : Matrix (Fin i) (Fin i) ℂ[X],
      M.adjugate.map (evalRingHom 0) = (M.map (evalRingHom 0)).adjugate := fun M =>
    (evalRingHom (0 : ℂ)).map_adjugate M
  have hC : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map C).map (evalRingHom 0) = M := fun M => by
    refine Matrix.ext fun a b => ?_
    simp
  have hmap : (kerPoly p i hi L).map (evalRingHom 0) = sigTop p i hi * tailForm p i hi L := by
    simp only [kerPoly, Matrix.map_mul, hadj, hV, hV', adjugate_one, Matrix.mul_one, hC]
  rw [coeff_zero_eq_eval_zero, ← hmap]
  simp [Matrix.trace, eval_finsetSum]
end GroundTheory.Heights₂.Heights.FourB
