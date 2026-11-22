-- Prove2me | solution 1 for ReciprocityTheory.Gal.isOpen_setOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:37.617606+00:00
-- url     : https://prove2.me/submissions/5ffaa547-8550-4257-b6dd-97672afcf376

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (x : Ω) (P : Ω → Prop) : IsOpen {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [isOpen_iff_forall_mem_open]
  intro τ hτ
  refine ⟨(fun σ => τ⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)),
    ?_, ?_, ?_⟩
  · intro σ hσ
    have hσ' : τ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup := hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
    have h1 := hσ' x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : σ x = τ x := by
      calc σ x = (τ * (τ⁻¹ * σ)) x := by rw [mul_inv_cancel_left]
        _ = τ ((τ⁻¹ * σ) x) := by rw [AlgEquiv.mul_apply]
        _ = τ x := by rw [h1]
    show P (σ x)
    rw [h2]
    exact hτ
  · exact hH.preimage (continuous_const.mul continuous_id)
  · show τ⁻¹ * τ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
end ReciprocityTheory.Gal
