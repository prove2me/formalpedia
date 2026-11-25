-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_of_homog_af572b81c448
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:09.309026+00:00
-- url     : https://prove2.me/submissions/8341b3a3-9b1f-42d3-bcdb-81da46285f62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a

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
theorem _root_.solution {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω)
    (c : (k : ι) → Fin (n k + 1)) {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ}
    (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (dehomCoords z c) G = aeval z G * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ b k :=
  aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z hG
end GroundTheory.Heights₂.Heights.OrbitChartMax
