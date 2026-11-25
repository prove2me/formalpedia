-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_maximalIdeal_iff_2f60d05acc3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:30.183839+00:00
-- url     : https://prove2.me/submissions/e72dc2dd-3682-42cf-93e9-62f1a7286712

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) (x : locRing P W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W)
    (hx : (x : FractionRing (MRing ι ⧸ P)) * fracHom P v = fracHom P u) :
    haveI := isLocalRing hPW
    x ∈ maximalIdeal (locRing P W) ↔ u ∈ W := by
  have := isLocalRing hPW
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff hPW x hu hv hvW hx, not_not]
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
