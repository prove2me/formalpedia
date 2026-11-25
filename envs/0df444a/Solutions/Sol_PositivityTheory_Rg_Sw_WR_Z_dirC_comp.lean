-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.dirC_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:26.236297+00:00
-- url     : https://prove2.me/submissions/31c0ebdc-efeb-4058-acc2-169d310aaec5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (G : MC n → ℂ) (y : E n) (hG : DifferentiableAt ℂ G (herm y)) (w : Fin n → Fin n → ℂ) :
    dirC (fun y => G (herm y)) w y =
      fderiv ℂ G (herm y) (hermL (fun a b => (w a b).re) + Complex.I • hermL (fun a b => (w a b).im)) := by
  have hd : HasFDerivAt (fun y => G (hermL y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp hermL) y :=
    (hG.hasFDerivAt.restrictScalars ℝ).comp y hermL.hasFDerivAt
  unfold dirC
  rw [show (fun y => G (herm y)) = fun y => G (hermL y) from rfl, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', map_add, map_smul,
    smul_eq_mul]
end PositivityTheory.Rg.Sw.WR.Z
