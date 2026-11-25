-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.eval_toMv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:48.186132+00:00
-- url     : https://prove2.me/submissions/8887906f-6573-4c36-b3af-ea122760f98d

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution {σ : Type} (i : σ) (p : Polynomial ℂ) (g : σ → ℂ) : eval g (toMv i p) = p.eval (g i) := by
  simp [toMv, Polynomial.eval_eq_sum_range, map_sum]
end PositivityTheory.SiegelWeilFormula.KLI
