-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:56.893239+00:00
-- url     : https://prove2.me/submissions/d3058af9-e636-4962-a4a3-b383f8f4a058

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


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
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (homogenize c F) (homDeg F) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hle : Finsupp.weight (coordDeg n) m ≤ homDeg F := fun k ↦
    Finset.le_sup (f := fun m ↦ Finsupp.weight (coordDeg n) m k) hm
  have h := (isWeightedHomogeneous_monomial (coordDeg n) m (coeff m F) rfl).mul
    (isWeightedHomogeneous_chartMonomial c (homDeg F - Finsupp.weight (coordDeg n) m))
  rwa [add_tsub_cancel_of_le hle] at h
end GroundTheory.Heights₂.Heights.OrbitChartMax
