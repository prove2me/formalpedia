-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.exists_unit_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:45.744215+00:00
-- url     : https://prove2.me/submissions/4d672d7b-64ad-4278-80ed-1bfddde1a02d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_exists_unit_param
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coe_ordZ
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_one

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
private theorem ordZ_one (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] : ordZ ϖ ζ (1 : A) = 0 := by
  have := coe_ordZ (ζ := ζ) h (one_mem (nonZeroDivisors A))
  rw [ord_one (ζ := ζ) h] at this
  exact_mod_cast this
private theorem ordZ_units_mul (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (v w : Aˣ) :
    ordZ ϖ ζ ((v : A) * w) = ordZ ϖ ζ v + ordZ ϖ ζ w := by
  have hv := coe_ordZ (ζ := ζ) h v.isUnit.mem_nonZeroDivisors
  have hw := coe_ordZ (ζ := ζ) h w.isUnit.mem_nonZeroDivisors
  have hvw := coe_ordZ (ζ := ζ) h (v * w).isUnit.mem_nonZeroDivisors
  rw [Units.val_mul, ord_mul (ζ := ζ) h, ← hv, ← hw] at hvw
  exact_mod_cast hvw
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
theorem _root_.solution (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (d : Pts O A → ℤ) :
    ∃ u : Aˣ, ∀ ζ : Pts O A, ord ϖ ζ (u : A) = ((d ζ : ℤ) : WithTop ℤ) := by
  classical
  haveI := Fintype.ofFinite (Pts O A)
  choose t ht using exists_unit_param K h
  let φ : Pts O A → Aˣ →* Multiplicative ℤ := fun ζ =>
    { toFun := fun v => Multiplicative.ofAdd (ordZ ϖ ζ (v : A))
      map_one' := by simp only [Units.val_one, ordZ_one h ζ]; rfl
      map_mul' := fun v w => by simp only [Units.val_mul, ordZ_units_mul h ζ v w]; rfl }
  refine ⟨∏ ζ', t ζ' ^ d ζ', fun ζ => ?_⟩
  have e2 : ∀ ζ', Multiplicative.toAdd (φ ζ (t ζ')) = if ζ = ζ' then 1 else 0 := by
    intro ζ'
    show ordZ ϖ ζ (t ζ' : A) = _
    have := coe_ordZ (ζ := ζ) h (t ζ').isUnit.mem_nonZeroDivisors
    rw [ht ζ' ζ] at this
    exact_mod_cast this
  have hz : ordZ ϖ ζ ((∏ ζ', t ζ' ^ d ζ' : Aˣ) : A) = d ζ := by
    have e1 : Multiplicative.toAdd (φ ζ (∏ ζ', t ζ' ^ d ζ')) =
        ordZ ϖ ζ ((∏ ζ', t ζ' ^ d ζ' : Aˣ) : A) := rfl
    rw [← e1, map_prod, toAdd_prod]
    simp only [map_zpow, toAdd_zpow, e2, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← coe_ordZ (ζ := ζ) h (Units.isUnit _).mem_nonZeroDivisors, hz]
end PI.UnitaryGroupMassFormula.BallQuotLen
