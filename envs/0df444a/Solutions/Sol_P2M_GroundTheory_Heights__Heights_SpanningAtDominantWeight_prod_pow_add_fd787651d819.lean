-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:51.287798+00:00
-- url     : https://prove2.me/submissions/03a47bba-8e30-449d-a3b3-4b2ed2b14c38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution {M : Type} [CommMonoid M] (z : Coord n → M) (μ₁ μ₂ : Coord n →₀ ℕ) :
    ∏ p, z p ^ (μ₁ + μ₂) p = (∏ p, z p ^ μ₁ p) * ∏ p, z p ^ μ₂ p := by
  simp [pow_add, Finset.prod_mul_distrib]
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
