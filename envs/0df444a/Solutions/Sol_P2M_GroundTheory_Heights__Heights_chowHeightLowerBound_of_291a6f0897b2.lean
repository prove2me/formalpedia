-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowHeightLowerBound_of_291a6f0897b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:28.095032+00:00
-- url     : https://prove2.me/submissions/86f9d5fb-8e5f-4c63-868d-e6ed63f4bfcf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_norm_pos_9178f4bb2177
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_vertTerm_nonneg_4d532362fa73
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_mem_linForm_not_mem_e4689351a404
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Classical
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hR : ChowHeightRecursion.Statement) (hS : ChowFormSection.Statement)
    (hB : BaseChangeLogBound.Statement) (hMul : ChowHeightMul.Statement) :
    ChowHeightLowerBound.Statement := by
  intro K _ _ n e₀ δ₀ H I₀ f₀ S Λ hI₀ hf₀ hδ₀ hspan hΛ
  set L : ℝ := (1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, Real.log (Λ σ) with hL
  have hd : (0 : ℝ) ≤ 1 / Module.finrank ℚ K := by positivity

  suffices claim : ∀ k : ℕ, ∀ (I : Ideal (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin k × Fin n) K)
      (δ : ℕ), IsProjPrime I → IsChowForm I k g → IsMultiHomog δ g → -((k * δ : ℕ) : ℝ) * L ≤ chowHt H k δ g by
    exact claim (e₀ + 1) I₀ f₀ δ₀ hI₀ hf₀ hδ₀
  intro k
  induction k with
  | zero =>
    intro I g δ _ hg _
    rw [chowHt_zero_groups_eq_zero H δ hg.1]
    simp
  | succ e ih =>
    intro I f δ hI hf hδ
    obtain ⟨s, hsS, hs⟩ := exists_mem_linForm_not_mem hI.isRelevant hspan
    have hrec := hR K n e δ H I f s hI hf hδ hs

    have hsec : -((e * δ : ℕ) : ℝ) * L ≤ chowHt H e δ (specFirst f fun j => (s j : K)) := by
      obtain ⟨c, hc, g, hg, heq⟩ := hS K n e I f (fun j => (s j : K)) hI hf hs
      have hne : specFirst f (fun j => (s j : K)) ≠ 0 := by
        rw [heq]
        exact mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW =>
          pow_ne_zero _ (hg W hW).1)
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        rw [chowHt_zero_groups_eq_zero H δ hne]
        simp
      · have hδs := hδ.specFirst (fun j => (s j : K))
        rw [heq] at hδs hne
        obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle he _ c g hg hδs hne
        rw [heq, ← hsum, chowHt_C_mul_prod hMul H _ _ _ _ (fun W hW => (hg W hW).1) hc]
        have hprime : ∀ W ∈ (divCycle I fun j => (s j : K)).support, IsProjPrime W := by
          intro W hW
          exact isProjPrime_of_mem_support_divCycle hI _ hW
        calc -(((e * ∑ W ∈ (divCycle I fun j => (s j : K)).support,
                (divCycle I fun j => (s j : K)) W * δW W : ℕ)) : ℝ) * L
            = ∑ W ∈ (divCycle I fun j => (s j : K)).support,
                ((divCycle I fun j => (s j : K)) W : ℝ) * (-((e * δW W : ℕ) : ℝ) * L) := by
              push_cast
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
              refine Finset.sum_congr rfl fun W _ => ?_
              ring
          _ ≤ _ := Finset.sum_le_sum fun W hW =>
              mul_le_mul_of_nonneg_left (ih W (g W) (δW W) (hprime W hW) (hg W hW) (hδW W hW))
                (Nat.cast_nonneg _)

    have harch : ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
        (fsLog (H.normAt σ) fun j => σ (s j)) ≤ δ * ∑ σ : K →+* ℂ, Real.log (Λ σ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun σ _ => ?_
      refine (hB K n e δ (H.normAt σ) I f (fun j => (s j : K)) σ hI hf hδ hs).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hne : (fun j => σ (s j : K)) ≠ 0 := by
        intro h0
        apply hs
        have : (fun j => (s j : K)) = 0 := funext fun j => σ.injective (by simpa using congrFun h0 j)
        rw [this]
        simp [linForm]
      exact Real.log_le_log (HermNorm.norm_pos _ hne) (hΛ s hsS σ)
    have hvert := vertTerm_nonneg I (e + 1) s
    rw [hrec]
    have : -(((e + 1) * δ : ℕ) : ℝ) * L = -((e * δ : ℕ) : ℝ) * L +
        (1 / Module.finrank ℚ K : ℝ) * (0 - δ * ∑ σ : K →+* ℂ, Real.log (Λ σ)) := by
      rw [hL]
      push_cast
      ring
    rw [this]
    gcongr
end GroundTheory.Heights₂.Heights
