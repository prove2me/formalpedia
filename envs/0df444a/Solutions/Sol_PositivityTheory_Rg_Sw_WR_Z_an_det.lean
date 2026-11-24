-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.an_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:39.594843+00:00
-- url     : https://prove2.me/submissions/78f5aa7a-a089-4223-9136-97b8bb3ab5ed

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
theorem _root_.solution {M : MC n → Matrix (Fin n) (Fin n) ℂ} {B₀ : MC n} (h : EntAn M B₀) :
    AnalyticAt ℂ (fun B => (M B).det) B₀ := by
  have e : (fun B => (M B).det) =
      ∑ σ : Equiv.Perm (Fin n), fun B => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M B (σ i) i := by
    funext B
    rw [det_apply', Finset.sum_apply]
  rw [e]
  refine Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_
  have e2 : (fun B => ∏ i, M B (σ i) i) = ∏ i, fun B => M B (σ i) i := by
    funext B
    rw [Finset.prod_apply]
  rw [e2]
  exact Finset.analyticAt_prod _ fun i _ => h (σ i) i
end PositivityTheory.Rg.Sw.WR.Z
