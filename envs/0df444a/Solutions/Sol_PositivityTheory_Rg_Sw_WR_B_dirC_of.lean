-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:23.597826+00:00
-- url     : https://prove2.me/submissions/f32dacb8-5d93-47f2-831a-fca72dacbf97

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {f : E n → ℂ} {f' : E n →L[ℝ] ℂ} {y : E n} (h : HasFDerivAt f f' y) (w : Fin n → Fin n → ℂ) :
    dirC f w y = f' (fun a b => (w a b).re) + Complex.I * f' (fun a b => (w a b).im) := by
  rw [dirC, h.fderiv]
end PositivityTheory.Rg.Sw.WR.B
