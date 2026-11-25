-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.contDiff_dirC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:15.721966+00:00
-- url     : https://prove2.me/submissions/4cb20765-9b84-4c0f-8338-64bb6ee2512c

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
theorem _root_.solution {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => dirC f w y) := by
  have h1 := (contDiff_infty_iff_fderiv.1 hf).2
  unfold dirC
  exact (h1.clm_apply contDiff_const).add (contDiff_const.mul (h1.clm_apply contDiff_const))
end PositivityTheory.Rg.Sw.WR.K.GB.TW
