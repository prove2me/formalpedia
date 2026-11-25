-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.isUnit_of_ord_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:39.253297+00:00
-- url     : https://prove2.me/submissions/b0cb3f53-28ae-4e71-987a-2197e3b433ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_eq_zero_of_ord_top
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A} (hx : ∀ ζ : Pts O A, ord ϖ ζ x ≠ ⊤) :
    IsUnit x := by
  have hnz : x ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine eq_zero_of_ord_top h (fun ζ => ?_)
    have := ord_mul (ζ := ζ) h x y
    rw [mul_comm x y, hy, ord_zero (ζ := ζ) h] at this
    rcases WithTop.add_eq_top.mp this.symm with h1 | h1
    · exact absurd h1 (hx ζ)
    · exact h1
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors hnz
end PI.UnitaryGroupMassFormula.BallQuotLen
