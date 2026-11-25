-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.dkl_comp_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:21.640702+00:00
-- url     : https://prove2.me/submissions/6b6256c2-b286-41b7-9c92-22ec060524a9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_hermL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_herm_re_im_vkl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (k l : Fin n) (y : Fin n → Fin n → ℝ) (hd : DifferentiableAt ℂ G (herm y)) :
    Dkl k l (fun y => G (herm y)) y = cpart l k G (herm y) := by
  have hG : HasFDerivAt G ((fderiv ℂ G (herm y)).restrictScalars ℝ) (herm y) :=
    hd.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => G (herm y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp (hermL n)) y :=
    hG.comp y (hermL n).hasFDerivAt
  unfold Dkl dirC cpart
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_re_im_vkl k l, map_add, map_smul, smul_eq_mul]
end PositivityTheory.Rg.Sw.WR.K.GB
