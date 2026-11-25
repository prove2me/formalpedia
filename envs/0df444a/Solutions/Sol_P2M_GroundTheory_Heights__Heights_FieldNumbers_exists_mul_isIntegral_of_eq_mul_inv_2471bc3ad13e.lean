-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_mul_isIntegral_of_eq_mul_inv_2471bc3ad13e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:17.241669+00:00
-- url     : https://prove2.me/submissions/cc007e3c-d307-40ba-b938-c1ead718273d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (R A : Subalgebra F Ω) (hRA : R ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    {x : Ω} (hx : IsIntegral A x) : ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ IsIntegral R (d * x) := by
  let M : Submonoid R :=
    { carrier := {d | (d : Ω) ≠ 0 ∧ (d : Ω)⁻¹ ∈ A}
      mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by
        rw [Subalgebra.coe_mul, mul_inv]; exact A.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_ne_zero, by rw [Subalgebra.coe_one, inv_one]; exact A.one_mem⟩ }
  let _ : Algebra R A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization M A := by
    refine (isLocalization_iff M A).mpr ⟨fun d => ?_, fun a => ?_, fun {a b} h => ⟨1, ?_⟩⟩
    · exact ⟨⟨_, ⟨_, d.2.2⟩, Subtype.ext (mul_inv_cancel₀ d.2.1), Subtype.ext (inv_mul_cancel₀ d.2.1)⟩, rfl⟩
    · obtain ⟨r, hr, d, hd, hd0, hdA, he⟩ := hloc a a.2
      refine ⟨(⟨r, hr⟩, ⟨⟨d, hd⟩, hd0, hdA⟩), Subtype.ext ?_⟩
      change (a : Ω) * d = r
      rw [he, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
    · have e : ((algebraMap R A a : A) : Ω) = (algebraMap R A b : A) := congrArg Subtype.val h
      have e' : (a : Ω) = b := e
      rw [Subtype.ext e']
  obtain ⟨⟨d, hd0, hdA⟩, hint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (M := M) (Rₘ := A) x hx
  exact ⟨d, d.2, hd0, hdA, hint⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
