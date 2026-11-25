-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_exists_injective_cone_3ee5f0062363
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:22.25194+00:00
-- url     : https://prove2.me/submissions/3a4b86e1-87dd-4e49-a7b5-28d5cb0bfe72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpanBundleTrdegGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_injective_aeval_mul_X_80cf88eaa3b4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpanBundleTrdegGe
theorem _root_.solution {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    (K : Type*) {i : ℕ} (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    ∃ Ψ : MvPolynomial (Fin i) (MvPolynomial K Ω) →+* MvPolynomial (Option K) Φ, Function.Injective Ψ ∧
      (∀ p, Ψ (C p) = rename some (map (algebraMap Ω Φ) p)) ∧ ∀ r, Ψ (X r) = C (σ r) * X none := by
  let θ : MvPolynomial (Fin i) Ω →+* Polynomial Φ :=
    (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ).toRingHom
  have hθ : Function.Injective θ := SpanBundleTrdegGe.injective_aeval_mul_X σ hσ
  let e := (optionEquivRight Φ K).symm
  have heC : ∀ a : Φ, e (C (Polynomial.C a)) = C a := fun a =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_C Φ K a).symm
  have heX : ∀ k, e (X k) = X (some k) := fun k =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_some Φ K k).symm
  have heN : e (C Polynomial.X) = X none :=
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_none Φ K).symm
  refine ⟨e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom),
    e.injective.comp ((map_injective θ hθ).comp (commAlgEquiv Ω (Fin i) K).injective), ?_, ?_⟩
  · intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h1 : θ (C a) = Polynomial.C (algebraMap Ω Φ a) := by simp [θ]
      simp [h1, heC]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p k hp =>
      rw [C_mul, map_mul, hp, map_mul, map_mul]
      have h2 : (e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom))
          (C (X k)) = X (some k) := by
        simp [heX]
      rw [h2, map_X, rename_X]
  · intro r
    have h3 : θ (X r) = Polynomial.C (σ r) * Polynomial.X := by simp [θ]
    have h4 : e (C (Polynomial.C (σ r) * Polynomial.X)) = C (σ r) * X none := by
      rw [C_mul, map_mul, heC, heN]
    simp [h3, heC, heN]
end SpanBundleTrdegGe
end GroundTheory.Heights₂.Heights.NumbersDVR
