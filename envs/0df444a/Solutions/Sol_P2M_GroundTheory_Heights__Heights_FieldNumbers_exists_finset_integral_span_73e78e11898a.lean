-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:32.290453+00:00
-- url     : https://prove2.me/submissions/2cd44559-5c74-45c2-99b0-90f9607756f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_mul_isIntegral_of_eq_mul_inv_2471bc3ad13e

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
open IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (hN : NoetherIntegralClosureFinite.Statement.{u})
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {S : Set Ω} (hS : S.Finite)
    (A : Subalgebra F Ω) (L : IntermediateField F Ω) (hRA : Algebra.adjoin F S ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin F S, ∃ d ∈ Algebra.adjoin F S,
      d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    (hEL : IntermediateField.adjoin F S ≤ L)
    (hfin : FiniteDimensional (IntermediateField.adjoin F S) (IntermediateField.extendScalars hEL)) :
    ∃ s : Finset Ω, (∀ e ∈ s, e ∈ L ∧ IsIntegral A e) ∧
      ∀ x ∈ L, IsIntegral A x → x ∈ Submodule.span A (s : Set Ω) := by
  classical
  let L' := IntermediateField.extendScalars hEL
  let _ : Algebra (Algebra.adjoin F S) L' :=
    ((algebraMap (IntermediateField.adjoin F S) L').comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S) L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType F (Algebra.adjoin F S) := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨t, ht⟩ := Module.finite_def.mp
    (hN F (Algebra.adjoin F S) (IntermediateField.adjoin F S) L')
  let ι₀ : L' →ₐ[Algebra.adjoin F S] Ω := { L'.val.toRingHom with commutes' := fun _ => rfl }
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective
  let _ : Algebra (Algebra.adjoin F S) A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨t.image fun y => ι₀ y.1, ?_, fun x hx hxA => ?_⟩
  · intro e he
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨(IntermediateField.mem_extendScalars hEL).mp y.1.2,
      ((isIntegral_algHom_iff ι₀ hι₀).mpr y.2).tower_top⟩
  obtain ⟨d, hd, hd0, hdA, hint⟩ := exists_mul_isIntegral_of_eq_mul_inv _ A hRA hloc hxA
  let z : integralClosure (Algebra.adjoin F S) L' :=
    ⟨⟨d * x, (IntermediateField.mem_extendScalars hEL).mpr
      (mul_mem (hEL (IntermediateField.algebra_adjoin_le_adjoin F S hd)) hx)⟩,
      (isIntegral_algHom_iff ι₀ hι₀).mp hint⟩
  have hz : ι₀ z ∈ Submodule.span (Algebra.adjoin F S) ((t.image fun y => ι₀ y.1 : Finset Ω) : Set Ω) := by
    have hzt : z ∈ Submodule.span (Algebra.adjoin F S) (t : Set _) := ht ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem
      (f := ι₀.toLinearMap.comp (integralClosure (Algebra.adjoin F S) L').val.toLinearMap) hzt
    rw [Submodule.map_span] at this
    rw [Finset.coe_image]
    exact this
  have e : (⟨d⁻¹, hdA⟩ : A) • (d * x) = x := by
    rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc]
    change d⁻¹ * d * x = x
    rw [inv_mul_cancel₀ hd0, one_mul]
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars (Algebra.adjoin F S) A _ hz)
end GroundTheory.Heights₂.Heights.FieldNumbers
