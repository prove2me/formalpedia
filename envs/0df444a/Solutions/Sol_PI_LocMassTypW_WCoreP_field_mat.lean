-- Prove2me | solution 1 for PI.LocMassTypW.WCoreP.field_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:28.666305+00:00
-- url     : https://prove2.me/submissions/7aefb54d-7f92-454d-8114-548c2a103c92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings
import Theorems.Thm_PI_LocMassTypW_WCoreP_field_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module
namespace PI.LocMassTypW.WCoreP
theorem _root_.solution {K : Type*} [Field K] {n m : ℕ} (A0 A B0 B : Matrix (Fin n) (Fin m) K)
    (L0 L M0 M : Matrix (Fin m) (Fin n) K) (hL0 : L0 * A0 = 1) (hL : L * A = 1)
    (hM0 : M0 * B0 = 1) (hM : M * B = 1) (hC : A0ᵀ * B0 = Aᵀ * B) :
    ∃ k : Matrix (Fin n) (Fin n) K, IsUnit k ∧ k * A0 = A ∧ Bᵀ * k = B0ᵀ := by
  have inj : ∀ {A' : Matrix (Fin n) (Fin m) K} {L' : Matrix (Fin m) (Fin n) K}, L' * A' = 1 →
      Function.Injective (Matrix.toLin' A') := by
    intro A' L' h x y hxy
    have h2 := congrArg (Matrix.toLin' L') hxy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h] using h2
  have sec : ∀ {B' : Matrix (Fin n) (Fin m) K} {M' : Matrix (Fin m) (Fin n) K}, M' * B' = 1 →
      ∀ w, Matrix.toLin' B'ᵀ (Matrix.toLin' M'ᵀ w) = w := by
    intro B' M' h w
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h]
  have hC' : Bᵀ * A = B0ᵀ * A0 := by
    have h := congrArg Matrix.transpose hC
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
    exact h.symm
  obtain ⟨e, he1, he2⟩ := field_core (Matrix.toLin' A0) (Matrix.toLin' A) (Matrix.toLin' B0ᵀ)
    (Matrix.toLin' Bᵀ) (Matrix.toLin' M0ᵀ) (Matrix.toLin' Mᵀ) (inj hL0) (inj hL) (sec hM0) (sec hM)
    (fun w => by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hC'])
  refine ⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_, ?_⟩
  · have h : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
        LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have h2 : (e : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) =
          LinearMap.id := by
        ext x
        simp
      rw [h2, LinearMap.toMatrix'_id]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)
  · rw [← LinearMap.toMatrix'_toLin' A0, ← LinearMap.toMatrix'_comp]
    have h : (e : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ Matrix.toLin' A0 = Matrix.toLin' A :=
      LinearMap.ext he1
    rw [h, LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_toLin' Bᵀ, ← LinearMap.toMatrix'_comp]
    have h : Matrix.toLin' Bᵀ ∘ₗ (e : (Fin n → K) →ₗ[K] (Fin n → K)) = Matrix.toLin' B0ᵀ :=
      LinearMap.ext he2
    rw [h, LinearMap.toMatrix'_toLin']
end PI.LocMassTypW.WCoreP
