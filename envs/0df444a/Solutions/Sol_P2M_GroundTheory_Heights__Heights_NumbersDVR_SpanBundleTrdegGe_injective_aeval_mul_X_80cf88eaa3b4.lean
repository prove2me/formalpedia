-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_injective_aeval_mul_X_80cf88eaa3b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:38.945974+00:00
-- url     : https://prove2.me/submissions/e6604e47-bb0d-42b8-805c-90125304fe77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpanBundleTrdegGe

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
theorem _root_.solution {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ] {i : ℕ}
    (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    Function.Injective (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) := by
  let H : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial (MvPolynomial (Fin i) Ω) :=
    aeval fun r => Polynomial.C (X r) * Polynomial.X
  have hH : Function.Injective H := by
    have h1 : ((Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω).comp H =
        AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro r
      simp [H]
    exact Function.LeftInverse.injective (g := (Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω)
      fun p => by rw [← AlgHom.comp_apply, h1, AlgHom.id_apply]
  have heq : (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) = (Polynomial.mapAlgHom (aeval σ)).comp H := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [H]
  rw [heq]
  exact (Polynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.1 hσ)).comp hH
end SpanBundleTrdegGe
end GroundTheory.Heights₂.Heights.NumbersDVR
