-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.intg_mono2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:32.715872+00:00
-- url     : https://prove2.me/submissions/31abe992-0f29-4fd9-a1ea-c042940feb4a

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_eval_monomial2
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad


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
theorem _root_.solution {b : ℂ} (hb : b.re < 0) (l μ : ℂ) (v : Fin 2 →₀ ℕ) (c : ℂ) :
    Integrable (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v c) * G2 b l μ p) := by
  have := ((intg_pow_quad hb (v 0) l).mul_prod (intg_pow_quad hb (v 1) μ)).const_mul c
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [G2, eval_monomial2]
  ring
end PositivityTheory.SiegelWeilFormula.KLI
