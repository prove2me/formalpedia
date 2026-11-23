-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_exists_hom____eq_9f8583d26737
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:28.262521+00:00
-- url     : https://prove2.me/submissions/5c3603df-da09-4802-89f3-2fdb3e525ec7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {A : Type u} [Category.{v} A] [Abelian A]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {A : Type u} [Category.{v} A] [Abelian A]
namespace GlobalTheory.Flasque
namespace _root_.GlobalTheory.Flasque
theorem _root_.solution {S T : ShortComplex A} (hS : S.ShortExact)
    [Injective T.X₂] (f : S.X₁ ⟶ T.X₁) : ∃ φ : S ⟶ T, φ.τ₁ = f := by
  have := hS.mono_f
  let τ₂ : S.X₂ ⟶ T.X₂ := Injective.factorThru (f ≫ T.f) S.f
  have h₂ : S.f ≫ τ₂ = f ≫ T.f := Injective.comp_factorThru _ _
  have hw : S.f ≫ τ₂ ≫ T.g = 0 := by
    rw [reassoc_of% h₂, T.zero, comp_zero]
  let τ₃ : S.X₃ ⟶ T.X₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ hw)
  have h₃ : S.g ≫ τ₃ = τ₂ ≫ T.g :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ _ hw) WalkingParallelPair.one
  exact ⟨{ τ₁ := f, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₂.symm, comm₂₃ := h₃.symm }, rfl⟩
end _root_.GlobalTheory.Flasque
end GlobalTheory.Flasque
