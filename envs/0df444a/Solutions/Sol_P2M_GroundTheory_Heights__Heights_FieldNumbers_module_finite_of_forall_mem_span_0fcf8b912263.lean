-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_module_finite_of_forall_mem_span_0fcf8b912263
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:25.661456+00:00
-- url     : https://prove2.me/submissions/f4b1e54d-3369-4803-9d87-18ef72e14387

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFinite

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
theorem _root_.solution {A A' B L : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing A'] [CommRing B] [Algebra A B] [CommRing L] [Algebra A' L] (φ : A →+* A')
    (hφ : Function.Surjective φ) (ψ : B →+* L) (hψ : Function.Injective ψ)
    (hcomm : ∀ a b, ψ (algebraMap A B a * b) = algebraMap A' L (φ a) * ψ b) (s : Finset L)
    (h : ∀ b, ψ b ∈ Submodule.span A' (s : Set L)) : Module.Finite A B := by
  let _ : Algebra A L := ((algebraMap A' L).comp φ).toAlgebra
  have hspan : ∀ x ∈ Submodule.span A' (s : Set L), x ∈ Submodule.span A (s : Set L) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add _ _ _ _ hy hz => exact add_mem hy hz
    | smul a' y _ hy =>
      obtain ⟨a, rfl⟩ := hφ a'
      have e : φ a • y = a • y := by rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [e]
      exact Submodule.smul_mem _ a hy
  let f : B →ₗ[A] L :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun a b => by rw [Algebra.smul_def, hcomm]; rfl }
  have : IsNoetherian A (Submodule.span A (s : Set L)) :=
    isNoetherian_span_of_finite A s.finite_toSet
  exact Module.Finite.of_injective (f.codRestrict _ fun b => hspan _ (h b))
    fun b c hbc => hψ (congrArg Subtype.val hbc)
end GroundTheory.Heights₂.Heights.FieldNumbers
