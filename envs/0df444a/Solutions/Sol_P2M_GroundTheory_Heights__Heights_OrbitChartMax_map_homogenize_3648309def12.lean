-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_map_homogenize_3648309def12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:09.685969+00:00
-- url     : https://prove2.me/submissions/db064d8b-2912-44f5-8ec1-fb6cdf096357

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax

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
theorem _root_.solution {R : Type*} [CommRing R] (c : (k : ι) → Fin (n k + 1))
    (φ : MvPolynomial (Coord n) ℤ →+* R) (hφ : ∀ k, φ (X ⟨k, c k⟩) = 1)
    (F : MvPolynomial (Coord n) ℤ) : φ (homogenize c F) = φ F := by
  conv_rhs => rw [F.as_sum]
  simp only [homogenize, map_sum, map_mul, chartMonomial, map_prod, map_pow, hφ, one_pow,
    Finset.prod_const_one, mul_one]
end GroundTheory.Heights₂.Heights.OrbitChartMax
