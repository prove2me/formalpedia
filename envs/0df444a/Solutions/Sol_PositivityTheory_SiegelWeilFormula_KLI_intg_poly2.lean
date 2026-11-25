-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.intg_poly2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:25.386852+00:00
-- url     : https://prove2.me/submissions/4928db69-b6cf-4ee3-aada-393c6407745a

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_mono2

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
theorem _root_.solution {b : ℂ} (hb : b.re < 0) (l μ : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) := by
  have e : (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) =
      fun p => ∑ v ∈ R.support, eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v (coeff v R)) * G2 b l μ p := by
    funext p
    conv_lhs => rw [R.as_sum]
    rw [map_sum, Finset.sum_mul]
  rw [e]
  exact integrable_finsetSum _ fun v _ => intg_mono2 hb l μ v _
end PositivityTheory.SiegelWeilFormula.KLI
