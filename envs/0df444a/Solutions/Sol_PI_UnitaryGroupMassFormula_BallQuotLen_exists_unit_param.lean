-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.exists_unit_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:49.194338+00:00
-- url     : https://prove2.me/submissions/5e336a1b-50ee-4dff-99af-3d558d71e53c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_isUnit_of_ord_ne_top
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_exists_param
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
open Classical
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (ζ₀ : Pts O A) :
    ∃ t : Aˣ, ∀ ζ : Pts O A, ord ϖ ζ (t : A) = (((if ζ = ζ₀ then 1 else 0 : ℤ)) : WithTop ℤ) := by
  obtain ⟨t, ht1, ht2⟩ := exists_param ζ₀
  have hord : ∀ ζ : Pts O A, ord ϖ ζ (t : A) = (((if ζ = ζ₀ then 1 else 0 : ℤ)) : WithTop ℤ) := by
    intro ζ
    rw [ord_of_mem (ζ := ζ) h t.2]
    split_ifs with hz
    · subst hz
      rw [show (⟨(t : A), t.2⟩ : ↥(As O A)) = t from rfl, ht1]
      rfl
    · rw [show (⟨(t : A), t.2⟩ : ↥(As O A)) = t from rfl, (vL_eq_zero_iff (ζ := ζ) t).mpr (ht2 ζ hz)]
      rfl
  have hu : IsUnit (t : A) :=
    isUnit_of_ord_ne_top K h (fun ζ => by rw [hord]; exact WithTop.coe_ne_top)
  exact ⟨hu.unit, fun ζ => by rw [hu.unit_spec]; exact hord ζ⟩
end PI.UnitaryGroupMassFormula.BallQuotLen
