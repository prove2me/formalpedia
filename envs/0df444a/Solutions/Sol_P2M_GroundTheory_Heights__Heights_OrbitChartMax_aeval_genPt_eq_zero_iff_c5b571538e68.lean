-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:44.134855+00:00
-- url     : https://prove2.me/submissions/34c675ee-ff92-47b5-91bc-308c4a81ab75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_55ccb4e49f3f

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
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
omit [Fintype ι] [DecidableEq ι] [V.IsPrime]
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution (F : MvPolynomial (Coord n) ℤ) : aeval (genPt V) F = 0 ↔ F ∈ V := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.OrbitChartMax
