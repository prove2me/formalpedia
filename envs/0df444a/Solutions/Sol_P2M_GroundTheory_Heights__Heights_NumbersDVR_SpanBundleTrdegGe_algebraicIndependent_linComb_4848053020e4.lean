-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_algebraicIndependent_linComb_4848053020e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:35.318027+00:00
-- url     : https://prove2.me/submissions/eb390031-0218-4d57-bf93-d4eb402dbd4d

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
theorem _root_.solution {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    {i : ℕ} (s : Fin i → Φ) (hs : AlgebraicIndependent Ω s) (A : Matrix (Fin i) (Fin i) Ω)
    (hA : IsUnit A) : AlgebraicIndependent Ω (fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) := by
  classical
  let L : Matrix (Fin i) (Fin i) Ω → MvPolynomial (Fin i) Ω →ₐ[Ω] MvPolynomial (Fin i) Ω :=
    fun B => aeval fun r => ∑ j, C (B r j) * X j
  have hcomp : ∀ B B', (L B').comp (L B) = L (B * B') := by
    intro B B'
    apply MvPolynomial.algHom_ext
    intro r
    simp only [L, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hid : L 1 = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, Matrix.one_apply]
  have heq : (aeval fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) = (aeval s).comp (L A) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, mul_comm]
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have hinj : Function.Injective (L A) := Function.LeftInverse.injective (g := L A⁻¹) fun p => by
    rw [← AlgHom.comp_apply, hcomp, hAinv, hid, AlgHom.id_apply]
  rw [algebraicIndependent_iff_injective_aeval, heq]
  exact (algebraicIndependent_iff_injective_aeval.1 hs).comp hinj
end SpanBundleTrdegGe
end GroundTheory.Heights₂.Heights.NumbersDVR
