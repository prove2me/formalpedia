-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.eq_zero_of_ord_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:44.063792+00:00
-- url     : https://prove2.me/submissions/b384687f-10f0-4e1f-9476-f790146b860a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
section Gen
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
private theorem enat_map_natCast_int_eq_top_iff (a : ℕ∞) : a.map (Nat.cast : ℕ → ℤ) = ⊤ ↔ a = ⊤ := by
  cases a <;> simp
variable {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V] {e : V}
end Gen
end PI.UnitaryGroupMassFormula.BallQuotLen
end

set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A}
    (hx : ∀ ζ : Pts O A, ord ϖ ζ x = ⊤) : x = 0 := by
  obtain ⟨n, hn⟩ := h.denom x
  have hy : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) = 0 := by
    refine eq_zero_of_localization _ (fun J hJ => ?_)
    have hv : vL (⟨J, hJ⟩ : Pts O A) ⟨ϖ ^ n • x, hn⟩ = ⊤ := by
      have := hx ⟨J, hJ⟩
      rw [ord_eq (ζ := (⟨J, hJ⟩ : Pts O A)) h hn, ordAt, WithTop.add_eq_top] at this
      rcases this with h1 | h1
      · exact (enat_map_natCast_int_eq_top_iff _).mp h1
      · exact absurd h1 WithTop.coe_ne_top
    exact (vL_eq_top_iff (ζ := (⟨J, hJ⟩ : Pts O A)) _).mp hv
  have h0 : ϖ ^ n • x = 0 := congrArg Subtype.val hy
  rw [Algebra.smul_def, map_pow] at h0
  exact (h.isUnit.pow n).mul_right_eq_zero.mp h0
end PI.UnitaryGroupMassFormula.BallQuotLen
