-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.exp_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:53.739823+00:00
-- url     : https://prove2.me/submissions/e5392cce-031a-486e-abd0-19e20771fb11

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrableRexpLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (a s : ℝ) : Real.exp (a * |s|) ≤ Real.exp (a * s) + Real.exp (-(a * s)) := by
  rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; have := Real.exp_pos (-(a * s)); linarith
  · rw [h]; have := Real.exp_pos (a * s); rw [show a * -s = -(a * s) by ring]; linarith
end PositivityTheory.SiegelWeilFormula.KFPB
