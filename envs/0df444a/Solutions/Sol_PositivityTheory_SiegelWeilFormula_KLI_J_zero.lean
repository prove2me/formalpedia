-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.J_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:13.759812+00:00
-- url     : https://prove2.me/submissions/d64c601c-9d66-4b63-a79c-04f9418fde7c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution {b : ℂ} (hb : b.re < 0) (c : ℂ) :
    J b 0 c = (Real.pi / -b) ^ (1 / 2 : ℂ) * cexp (-(c ^ 2 / (4 * b))) := by
  have := integral_cexp_quadratic hb c 0
  simp only [add_zero, zero_sub] at this
  simpa [J] using this
end PositivityTheory.SiegelWeilFormula.KLI
