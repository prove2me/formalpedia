-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coe_chartEval_289cf14dcdc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:26.639745+00:00
-- url     : https://prove2.me/submissions/87325c36-c3ac-49cc-b32a-f445a84fcc61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  have h : (((ratioField x).val.restrictScalars ℤ).comp (chartRing x c).val).comp (chartEval x c) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) :=
    algHom_ext fun p ↦ by simp [chartEval, chartRatio]
  exact DFunLike.congr_fun h f
end GroundTheory.Heights₂.Heights
