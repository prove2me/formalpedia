-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.entAn_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:28.474292+00:00
-- url     : https://prove2.me/submissions/4b82245f-8687-4c0e-857e-d10bac8db9a3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_entry

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
theorem _root_.solution (B₀ : MC n) : EntAn (fun B : MC n => 1 + Matrix.of B * Matrix.of B) B₀ := fun i j => by
  simp only [Matrix.add_apply, Matrix.mul_apply, of_apply]
  refine analyticAt_const.add ?_
  have e : (fun B : MC n => ∑ k, B i k * B k j) = ∑ k, fun B : MC n => B i k * B k j := by
    funext B
    rw [Finset.sum_apply]
  rw [e]
  exact Finset.analyticAt_sum _ fun k _ => (an_entry i k B₀).mul (an_entry k j B₀)
end PositivityTheory.Rg.Sw.WR.Z
