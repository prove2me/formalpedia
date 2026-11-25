-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.differentiable_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:40.828901+00:00
-- url     : https://prove2.me/submissions/0d8a95b4-04bd-4583-96b9-d04a50aa273f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ f :=
  hf.differentiable (by simp)
end PositivityTheory.Rg.Sw.WR.T
