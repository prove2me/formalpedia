-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_differentiableOn_polyEval_2217afe5cc1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:28.314014+00:00
-- url     : https://prove2.me/submissions/d4af0ea2-f615-40ee-adca-f1b5fc7d8781

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
theorem _root_.solution (P : Polynomial (MvPolynomial (Fin d) ℂ)) {ψ : (Fin d → ℂ) → ℂ}
    {U : Set (Fin d → ℂ)} (hψ : DifferentiableOn ℂ ψ U) :
    DifferentiableOn ℂ (fun w => (P.map (eval w)).eval (ψ w)) U := by
  have h : (fun w => (P.map (eval w)).eval (ψ w)) =
      fun w => ∑ i ∈ Finset.range (P.natDegree + 1), eval w (P.coeff i) * ψ w ^ i := by
    funext w
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [h]
  exact DifferentiableOn.fun_sum fun i _ =>
    ((AnalyticOnNhd.eval_mvPolynomial (P.coeff i)).differentiableOn.mono (Set.subset_univ _)).mul
      (hψ.pow i)
end GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
