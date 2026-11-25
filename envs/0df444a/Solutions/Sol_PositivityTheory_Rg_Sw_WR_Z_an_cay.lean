-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.an_cay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:27.199788+00:00
-- url     : https://prove2.me/submissions/ca6a7893-ff79-44ce-aa9d-1b1f62ffa406

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
theorem _root_.solution (U : Set (MC n)) (hU : IsOpen U) (G : MC n → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (cay G) U := by
  intro B hB
  have e : cay G = ∑ σ : Equiv.Perm (Fin n),
      fun B => ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n G B (fun k => eU (σ k) k) := by
    funext B
    unfold cay
    rw [Finset.sum_apply]
  rw [e]
  exact Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul
    (((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => MC n) ℂ (fun k => eU (σ k) k)).analyticAt _).comp
      ((hG.iteratedFDeriv_of_isOpen hU n) B hB))
end PositivityTheory.Rg.Sw.WR.Z
