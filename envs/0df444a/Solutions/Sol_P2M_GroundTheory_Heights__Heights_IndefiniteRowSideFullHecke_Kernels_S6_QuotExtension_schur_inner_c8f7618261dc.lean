-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_schur_inner_c8f7618261dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:41.402966+00:00
-- url     : https://prove2.me/submissions/90f5a82a-c264-49b9-a541-8f5e93fb9dcf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
theorem _root_.solution {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (G : Matrix (m ⊕ k) (m ⊕ k) ℂ) (hA : IsUnit G.toBlocks₁₁.det) (β β' : m → ℂ) (γ γ' : k → ℂ)
    (h : ∀ i, (G *ᵥ Sum.elim β' γ') (Sum.inl i) = 0) :
    star (Sum.elim β γ) ⬝ᵥ (G *ᵥ Sum.elim β' γ') =
      star γ ⬝ᵥ ((G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ γ') := by
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  set D := G.toBlocks₂₂
  have hG : G = fromBlocks A B C D := (fromBlocks_toBlocks G).symm
  have hv : G *ᵥ Sum.elim β' γ' = Sum.elim (A *ᵥ β' + B *ᵥ γ') (C *ᵥ β' + D *ᵥ γ') := by
    rw [hG, fromBlocks_mulVec]
    rfl
  have h0 : A *ᵥ β' + B *ᵥ γ' = 0 := funext fun i => by simpa [hv] using h i
  have hβ : β' = -((A⁻¹ * B) *ᵥ γ') := by
    have hinv : A⁻¹ *ᵥ (A *ᵥ β') = β' := by rw [mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec]
    rw [← hinv, eq_neg_iff_add_eq_zero, ← mulVec_mulVec, ← mulVec_add, h0, mulVec_zero]
  have hw : C *ᵥ β' + D *ᵥ γ' = (D - C * A⁻¹ * B) *ᵥ γ' := by
    rw [hβ, mulVec_neg, mulVec_mulVec, sub_mulVec, Matrix.mul_assoc]
    abel
  rw [hv, h0, hw]
  simp [dotProduct, Fintype.sum_sum_type]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
