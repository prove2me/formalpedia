-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.quad_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:24.73545+00:00
-- url     : https://prove2.me/submissions/1c381a08-b034-4343-b745-0ab52155e2a1

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Theorems.Thm_PositivityTheory_ThKR_LL_bl_apply
import Theorems.Thm_PositivityTheory_ThKR_LL_fou_mq_fouInv
import Theorems.Thm_GlobalTheory_RealWeil_quad_fromBlocks
import Theorems.Thm_PositivityTheory_ThKR_LL_mq_apply
import Theorems.Thm_PositivityTheory_ThKR_LL_vf_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (f : Sch l) :
    quad X f = mq (bl Sum.inr Sum.inl X) f + vf (-bl Sum.inl Sum.inl X) f +
      fou l (mq (-bl Sum.inl Sum.inr X) (fouInv l f)) - ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f := by
  ext x
  have h := quad_fromBlocks (A := X.toBlocks₁₁) (B := X.toBlocks₁₂) (C := X.toBlocks₂₁) (D := X.toBlocks₂₂)
    (by rwa [fromBlocks_toBlocks]) f x
  rw [fromBlocks_toBlocks] at h
  have h2 := fou_mq_fouInv X.toBlocks₁₂ f
  have h3 : vf (-bl Sum.inl Sum.inl X) f x =
      -∑ j, ∑ k, (X.toBlocks₁₁ j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : Eu l)} f) x := by
    have : bl Sum.inl Sum.inl X x = ∑ j, ∑ k, (X.toBlocks₁₁ j k * x k) • (EuclideanSpace.single j 1 : Eu l) := by
      ext a
      simp [bl_apply, Pi.single_apply, toBlocks₁₁, Finset.sum_apply]
    rw [vf_apply, ContinuousLinearMap.neg_apply, this]
    simp [lineDerivOp_apply_eq_fderiv]
  have h4 : mq (bl Sum.inr Sum.inl X) f x = -(π * I * ∑ j, ∑ k, (X.toBlocks₂₁ j k : ℂ) * x j * x k * f x) := by
    have : ⟪x, bl Sum.inr Sum.inl X x⟫ = x ⬝ᵥ X.toBlocks₂₁ *ᵥ x := inner_toEuclideanCLM _ _ _
    rw [mq_apply, this]
    simp only [dotProduct, mulVec]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [SchwartzMap.sub_apply, SchwartzMap.add_apply]
  rw [h, h3, h4]
  erw [h2]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul]
  push_cast
  ring
end PositivityTheory.ThKR.LL
