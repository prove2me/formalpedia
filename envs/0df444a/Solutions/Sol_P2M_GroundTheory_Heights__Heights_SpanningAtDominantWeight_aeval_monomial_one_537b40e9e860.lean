-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:50.754804+00:00
-- url     : https://prove2.me/submissions/2d935c4a-01fb-4e15-9131-399eaa909c88

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
theorem _root_.solution {R : Type} [CommRing R] (z : Coord n → R) (μ : Coord n →₀ ℕ) :
    aeval z (monomial μ (1 : ℤ)) = ∏ p, z p ^ μ p := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_one, one_mul]
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
