-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.delta_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:14.346421+00:00
-- url     : https://prove2.me/submissions/3d3c6afa-25c7-4695-b712-2165e43fb27c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_foldr_herm

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
theorem _root_.solution (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) :
    Delta (fun y => F (herm y)) = fun y => DeltaC F (herm y) := by
  funext y
  simp only [Delta, DeltaC, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [(foldr_herm σ hU hF hh _).1]
end PositivityTheory.Rg.Sw.WR.K.GB
