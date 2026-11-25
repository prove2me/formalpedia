-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_smooth_adjoin_of_transcendental_1b0cb7f0067d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:25.000239+00:00
-- url     : https://prove2.me/submissions/69a8aa99-8d30-4055-976b-fcb39f71907e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution {A : Type} [Field A] [Algebra ℚ A] {v : A}
    (hv : Transcendental ℚ v) (s : Set A) (hs : Algebra.adjoin ℚ s = Algebra.adjoin ℚ {v}) :
    Algebra.Smooth ℚ (Algebra.adjoin ℚ s) := by
  have : Algebra.Smooth ℚ (Polynomial ℚ) := {}
  have e2 : (Polynomial.aeval v).range = Algebra.adjoin ℚ s := by
    rw [hs, Algebra.adjoin_singleton_eq_range_aeval]
  exact Algebra.Smooth.of_equiv ((AlgEquiv.ofInjective (Polynomial.aeval v)
    (transcendental_iff_injective.mp hv)).trans (Subalgebra.equivOfEq _ _ e2))
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
