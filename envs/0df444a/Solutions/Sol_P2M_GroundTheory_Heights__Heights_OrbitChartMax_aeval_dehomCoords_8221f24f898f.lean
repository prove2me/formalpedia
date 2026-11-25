-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_8221f24f898f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:19.466292+00:00
-- url     : https://prove2.me/submissions/860a2efd-ef5d-406d-aa1d-b5e91af91f27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_map_homogenize_3648309def12

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
theorem _root_.solution {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    aeval (dehomCoords z c) F =
      aeval z (homogenize c F) * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ homDeg F k := by
  change (aeval (dehomCoords z c)).toRingHom F = _
  rw [← map_homogenize c (aeval (dehomCoords z c)).toRingHom (fun k ↦ by
    simp [dehomCoords, inv_mul_cancel₀ (hz k)]) F]
  exact aeval_mul_of_homog (fun k ↦ (z ⟨k, c k⟩)⁻¹) z (isWeightedHomogeneous_homogenize c F)
end GroundTheory.Heights₂.Heights.OrbitChartMax
