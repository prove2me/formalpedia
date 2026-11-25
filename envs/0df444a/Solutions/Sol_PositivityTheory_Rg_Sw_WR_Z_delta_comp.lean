-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.delta_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:12:01.202721+00:00
-- url     : https://prove2.me/submissions/49d67bd9-68df-4de7-aa6c-25452a4a2f4e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_foldr_fderiv_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_foldr_Dkl

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
theorem _root_.solution (U : Set (MC n)) (hU : IsOpen U) (hherm : ∀ y : E n, (herm y : MC n) ∈ U) (G : MC n → ℂ)
    (hG : AnalyticOnNhd ℂ G U) : Delta (fun y => G (herm y)) = fun y => cay G (herm y) := by
  funext y
  unfold Delta cay
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := congrFun (foldr_Dkl σ U hU hherm G hG (List.finRange n)).2 y
  have h2 := (foldr_fderiv_eq G U hU hG n (fun k => eU (σ k) k)).2 _ (hherm y)
  rw [Pi.smul_apply, h1, h2, smul_eq_mul]
end PositivityTheory.Rg.Sw.WR.Z
