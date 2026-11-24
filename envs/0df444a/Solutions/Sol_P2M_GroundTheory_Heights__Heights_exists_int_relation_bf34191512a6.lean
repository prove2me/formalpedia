-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:48.881696+00:00
-- url     : https://prove2.me/submissions/f5fc2816-8cd8-4ecc-b8d7-683eb88e9ac8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree

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
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : AlgebraicClosure ℚ) :
    ∃ g : Polynomial ℤ, g ≠ 0 ∧ Polynomial.aeval r g = 0 :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)
end GroundTheory.Heights₂.Heights
