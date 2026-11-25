-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_dPpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:23.452461+00:00
-- url     : https://prove2.me/submissions/90283629-40a0-4d1a-8ce6-e3114bb4d08d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_det_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_herm_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_one_add_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (z : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) := by
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((dP y : ℝ) : ℂ)) := by
    have : (fun y : E n => ((dP y : ℝ) : ℂ)) = fun y => (1 + herm y * herm y).det :=
      funext fun y => (det_one_add_eq y).symm
    rw [this]
    refine contDiff_det_of fun a b => ?_
    simp only [Matrix.add_apply, Matrix.mul_apply]
    exact contDiff_const.add (ContDiff.sum fun c _ => (contDiff_herm_entry a c).mul (contDiff_herm_entry c b))
  have e : (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) = fun y => Complex.exp (Complex.log ((dP y : ℝ) : ℂ) * (-z)) :=
    funext fun y => Complex.cpow_def_of_ne_zero (by exact_mod_cast (dP_pos y).ne') _
  rw [e]
  refine ContDiff.cexp (ContDiff.mul ?_ contDiff_const)
  rw [contDiff_iff_contDiffAt]
  intro y
  exact ((Complex.contDiffAt_log (Complex.ofReal_mem_slitPlane.mpr (dP_pos y))).restrict_scalars ℝ).comp y hP.contDiffAt
end PositivityTheory.Rg.Sw.WR.B
