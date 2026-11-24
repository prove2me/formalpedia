-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.eval_monomial2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:53.331312+00:00
-- url     : https://prove2.me/submissions/9862710f-28ab-4f7b-85eb-0991138d91ce

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
theorem _root_.solution (v : Fin 2 →₀ ℕ) (c : ℂ) (x y : ℝ) :
    eval ![(x : ℂ), (y : ℂ)] (monomial v c) = c * ((x : ℂ) ^ v 0 * (y : ℂ) ^ v 1) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two]
end PositivityTheory.SiegelWeilFormula.KLI
