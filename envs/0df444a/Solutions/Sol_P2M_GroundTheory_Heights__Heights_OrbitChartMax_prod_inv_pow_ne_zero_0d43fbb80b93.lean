-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_prod_inv_pow_ne_zero_0d43fbb80b93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:35.161358+00:00
-- url     : https://prove2.me/submissions/00803d5c-1761-4ddb-9cf9-d7649ba58827

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
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution {Ω : Type*} [Field Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (D : ι → ℕ) : ∏ k, (z ⟨k, c k⟩)⁻¹ ^ D k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (inv_ne_zero (hz k))
end GroundTheory.Heights₂.Heights.OrbitChartMax
