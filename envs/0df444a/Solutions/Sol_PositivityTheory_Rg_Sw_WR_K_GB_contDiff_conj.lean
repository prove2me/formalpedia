-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.contDiff_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:53.614826+00:00
-- url     : https://prove2.me/submissions/faedeb27-1816-49ea-a168-854f4f619898

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_conjL_apply

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
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (k : Mc n) : ContDiff ℂ (⊤ : ℕ∞) (fun c : Mc n => k * c * kᴴ) := by
  have : (fun c : Mc n => k * c * kᴴ) = (LinearMap.toContinuousLinearMap (conjL k) : Mc n → Mc n) := by
    funext c; simp [conjL_apply]
  rw [this]; exact ContinuousLinearMap.contDiff _
end PositivityTheory.Rg.Sw.WR.K.GB
