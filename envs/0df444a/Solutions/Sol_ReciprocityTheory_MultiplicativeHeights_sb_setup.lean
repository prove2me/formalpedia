-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_setup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:44.716269+00:00
-- url     : https://prove2.me/submissions/893974f7-0858-48d1-8a45-53b4eea879e9

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_normSq_nonneg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dn_mul_Dn
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dn_mul_Dp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dp_mul_Dn
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dp_mul_Dp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_J_mul_J
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_negSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_posSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_re_dot_J


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix Module
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r p : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} {s : ℝ} (hH : H.PosDef)
    (hJ : H * signMat p r * H = signMat p r)
    (hP : ∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) :
    ∀ w : Fin r → ℂ, ∃ x, signMat p r *ᵥ (H *ᵥ x) = x ∧ sbDp p r *ᵥ x = sbDp p r *ᵥ w := by
  intro w
  have hJJ : signMat p r * signMat p r = 1 := sb_J_mul_J p r
  have hA2 : signMat p r * H * (signMat p r * H) = 1 := by
    calc signMat p r * H * (signMat p r * H) = signMat p r * (H * signMat p r * H) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have hHx : ∀ x : Fin r → ℂ, H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
    intro x; rw [mulVec_mulVec, hJJ, one_mulVec]
  have hre : ∀ x : Fin r → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx
    have := hH.re_dotProduct_pos hx
    simpa using this
  have hplus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = x → sbDp p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, sb_re_dot_J, sb_posSq_eq, hDx, sb_negSq_eq] at h1
    have h2 := sb_normSq_nonneg (sbDn p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  have hminus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = -x → sbDn p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, mulVec_neg, dotProduct_neg, Complex.neg_re, sb_re_dot_J, sb_posSq_eq,
      sb_negSq_eq, hDx] at h1
    have h2 := sb_normSq_nonneg (sbDp p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin r) ℂ, P = (1 / 2 : ℂ) • (1 + signMat p r * H) :=
    ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin r) (Fin r) ℂ, N = (1 / 2 : ℂ) • (1 - signMat p r * H) :=
    ⟨_, rfl⟩
  have hAP : signMat p r * H * P = P := by
    rw [hP, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hA2, add_comm]
  have hAN : signMat p r * H * N = -N := by
    rw [hN, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hA2, ← smul_neg, neg_sub]
  have hPN : P + N = 1 := by
    rw [hP, hN]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hPv : ∀ x, signMat p r *ᵥ (H *ᵥ (P *ᵥ x)) = P *ᵥ x := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAP]
  have hNv : ∀ x, signMat p r *ᵥ (H *ᵥ (N *ᵥ x)) = -(N *ᵥ x) := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAN, neg_mulVec]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin r) (Fin r) ℂ, F = sbDp p r * P + sbDn p r * N := ⟨_, rfl⟩
  have hFp : ∀ x, sbDp p r *ᵥ (F *ᵥ x) = sbDp p r *ᵥ (P *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dp_mul_Dp,
      sb_Dp_mul_Dn, zero_mul, zero_mulVec, add_zero]
  have hFn : ∀ x, sbDn p r *ᵥ (F *ᵥ x) = sbDn p r *ᵥ (N *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dn_mul_Dn,
      sb_Dn_mul_Dp, zero_mul, zero_mulVec, zero_add]
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    have h0 : F *ᵥ (x - y) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy
    have hp : P *ᵥ (x - y) = 0 := hplus _ (hPv _) (by rw [← hFp, h0, mulVec_zero])
    have hn : N *ᵥ (x - y) = 0 := hminus _ (hNv _) (by rw [← hFn, h0, mulVec_zero])
    have : x - y = 0 := by
      rw [← one_mulVec (x - y), ← hPN, add_mulVec, hp, hn, add_zero]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective F.mulVec :=
    mulVec_surjective_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨x, hx⟩ := hsurj (sbDp p r *ᵥ w)
  refine ⟨P *ᵥ x, hPv x, ?_⟩
  rw [← hFp, hx, mulVec_mulVec, sb_Dp_mul_Dp]
end ReciprocityTheory.MultiplicativeHeights
