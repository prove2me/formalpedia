-- Prove2me | solution 1 for P2M_GlobalTheory_UnitCocycle_lmul__eq_one_7cd501a29069
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:02.291901+00:00
-- url     : https://prove2.me/submissions/276c4acb-ad6f-482a-85a6-e99b96fb3524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
namespace GlobalTheory.UnitCocycle
theorem _root_.solution {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : Algebra.TensorProduct.lmul' R c = (1 : B) := by
  let μ : B ⊗[R] B →ₐ[R] B := Algebra.TensorProduct.lmul' R
  let ν : B ⊗[R] (B ⊗[R] B) →ₐ[R] B :=
    μ.comp (Algebra.TensorProduct.map (AlgHom.id R B) μ)
  have h12 : ν.comp (m₁₂ R B) = μ := by ext <;> simp [ν, μ, m₁₂, Algebra.TensorProduct.one_def]
  have h13 : ν.comp (m₁₃ R B) = μ := by ext <;> simp [ν, μ, m₁₃, Algebra.TensorProduct.one_def]
  have h23 : ν.comp (m₂₃ R B) = μ := by ext <;> simp [ν, μ, m₂₃, Algebra.TensorProduct.one_def]
  have h' := congrArg ν h
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, h12, h13, h23] at h'
  exact (hu.map μ).mul_left_cancel (by rw [mul_one]; exact h'.symm)
end GlobalTheory.UnitCocycle
