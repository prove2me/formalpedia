-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:27.17988+00:00
-- url     : https://prove2.me/submissions/ee259b7b-a7ac-4243-b33f-60dd9a5d3f88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffDominated
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.CutOffDominated
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f g : (Fin n → ℂ) → ℝ} (h : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    chartDens J A f φ = chartDens J A g φ := by
  funext y
  unfold chartDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]
end GroundTheory.Heights₂.Heights.CutOffDominated
