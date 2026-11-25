-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.ord_sub_one_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:25.467703+00:00
-- url     : https://prove2.me/submissions/16002c6a-7085-4a27-a2ab-0e051b6248b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_of_mem
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_zero_iff


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
theorem _root_.solution (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (x : ↥(As O A)) :
    0 ≤ ord ϖ ζ (x : A) + ((-1 : ℤ) : WithTop ℤ) ↔ x ∈ ζ.asIdeal := by
  rw [ord_of_mem (ζ := ζ) h x.2]
  have e := vL_eq_zero_iff (ζ := ζ) x
  rw [← not_not (a := x ∈ ζ.asIdeal), ← e]
  show 0 ≤ (vL ζ x).map (Nat.cast : ℕ → ℤ) + ((-1 : ℤ) : WithTop ℤ) ↔ ¬ vL ζ x = 0
  generalize vL ζ x = v
  induction v using ENat.recTopCoe with
  | top => simp
  | coe n =>
    simp only [ENat.map_coe, ← WithTop.coe_add, WithTop.coe_nonneg, Nat.cast_eq_zero]
    constructor <;> intro hh <;> omega
end PI.UnitaryGroupMassFormula.BallQuotLen
