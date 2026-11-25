-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.contDiff_sh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:17.85825+00:00
-- url     : https://prove2.me/submissions/678e76f2-56e3-4d7c-a0d2-e8b897080996

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sh c j) := by
  cases j with
  | zero => exact contDiff_const
  | succ j => exact hc j
end PositivityTheory.Rg.Sw.WR.K.GB.TW
