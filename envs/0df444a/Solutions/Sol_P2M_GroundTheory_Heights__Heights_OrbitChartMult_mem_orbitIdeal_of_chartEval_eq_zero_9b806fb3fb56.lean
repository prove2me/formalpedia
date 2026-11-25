-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_orbitIdeal_of_chartEval_eq_zero_9b806fb3fb56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:03.657965+00:00
-- url     : https://prove2.me/submissions/005782bd-0f69-4c82-bdd4-652a26e3a1db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2

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
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (hc : ∀ k, x k (c k) ≠ 0)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (h0 : chartEval x c F = 0) : F ∈ orbitIdeal x := by
  rw [← chartCone_eq_zero_iff x c hc, chartCone_of_isWeightedHomogeneous x c _ hF, h0]
  simp
end GroundTheory.Heights₂.Heights.OrbitChartMult
