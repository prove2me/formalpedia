-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.integrable_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:53.727415+00:00
-- url     : https://prove2.me/submissions/b3ed849c-49f6-49b1-b626-607509810433

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution {g : E n → ℂ} (hg : Continuous g) {h : E n → ℝ} (hh : Integrable h)
    (hb : ∀ y, ‖g y‖ ≤ h y) : Integrable g :=
  hh.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
end PositivityTheory.Rg.Sw.WR.Ib
