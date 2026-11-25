-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.deg_toMv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:42.612067+00:00
-- url     : https://prove2.me/submissions/4d333e19-4ca1-43d8-9214-205cfe20fba3

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
theorem _root_.solution {σ : Type} (i : σ) (p : Polynomial ℂ) : (toMv i p).totalDegree ≤ p.natDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_pow _ _).trans ?_
  have := Finset.mem_range.mp hj
  have h1 : (X i : MvPolynomial σ ℂ).totalDegree ≤ 1 := by rw [totalDegree_X]
  nlinarith
end PositivityTheory.SiegelWeilFormula.KLI
