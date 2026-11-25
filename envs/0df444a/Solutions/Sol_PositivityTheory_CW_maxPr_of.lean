-- Prove2me | solution 1 for PositivityTheory.CW.maxPr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:32.45902+00:00
-- url     : https://prove2.me/submissions/629484df-bc94-4623-83d0-2d5e100515d8

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_PMaxPr
import Theorems.Thm_PositivityTheory_CW_PMaxPr_hilbert_schmidt_nonneg_alt
import Theorems.Thm_PositivityTheory_CW_PMaxPr_evalAt_apply
import Theorems.Thm_PositivityTheory_CW_PMaxPr_sq_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.CW.PMaxPr.evalAt_apply

set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PMaxPr
namespace PositivityTheory.CW
theorem _root_.solution : CasimirIsRealScalar → EigenbasisExists → A13 → UnitaryGroupFacts → MaximumPrincipleVar → SumSquaresSecondDerivative → B5 → MaxPr := by
  intro hA3c hA11a hA13 _ hB4a hB4b hB5 n ε V _ _ E hM N
  classical
  obtain ⟨κ, hκ⟩ := hA3c n ε V E hM
  obtain ⟨ι, b, μ, hb⟩ := hA11a n ε V E hM
  obtain ⟨c, hc0, hc⟩ := hB4a n ε (2 * N)
  obtain ⟨s, x₀, C₁, hs, hC₁, h13⟩ := hA13 n ε V E hM ι b μ hb κ hκ (c / 2) (div_nonneg hc0 (by norm_num))
  have hTfin : {i | μ i < x₀}.Finite := (hb.fin x₀).subset fun i (hi : μ i < x₀) => show μ i ≤ x₀ from le_of_lt hi
  have hT : ∀ i, i ∈ hTfin.toFinset ↔ μ i < x₀ := fun i => by simp
  have hW1 : 0 ≤ (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    pow_nonneg (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) _
  have hKK : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) hW1
  refine ⟨s, Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)),
    hTfin.toFinset.image b, Real.sqrt_nonneg _, ?_⟩
  intro F hcont hder hgrow B hB hI v
  have hA0 : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) (sq_nonneg B)
  choose Cf hCf using hgrow
  have key : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) →
      ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) 1‖ ^ 2 ≤
        (Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)) * B) ^ 2 := by
    intro R S hS
    have hcu : ContinuousOn (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) (UJset ε) :=
      continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hcont (b i)).norm.pow 2)
    have hgu : ∃ C : ℝ, ∀ g ∈ UJset ε,
        (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) ≤ C * (1 + hs2 g) ^ (2 * N) := by
      refine ⟨∑ i ∈ S, phiR s R (μ i) * Cf (b i) ^ 2, fun g hg => ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sq_bound _ _ _ _ (hCf (b i) g hg) (norm_nonneg _)) (le_max_right _ _)
    have hdu : ∀ g ∈ UJset ε, ∃ d : Fin n × Fin n → ℝ,
        (∀ p ∈ nc ε, ∃ u' : ℝ → ℝ, (∀ t, HasDerivAt (fun t : ℝ =>
          ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2))‖ ^ 2) (u' t) t) ∧
          HasDerivAt u' (d p) 0) ∧
        c * (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) -
          2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 * (1 + hs2 g) ^ (2 * N) ≤ ∑ p ∈ nc ε, d p := by
      intro g hg
      obtain ⟨d, hd, hsum⟩ := hB4b n ε V E hM ι b μ hb κ hκ F hder S (fun i => phiR s R (μ i)) g hg
      refine ⟨d, hd, ?_⟩
      rw [hsum]
      have h13g := h13 R (evalAt g F) S hTfin.toFinset hS hT
      simp only [evalAt_apply] at h13g
      have hTb : ∑ i ∈ hTfin.toFinset, ‖F (b i) g‖ ^ 2 ≤
          hTfin.toFinset.card • (B ^ 2 * (1 + hs2 g) ^ (2 * N)) :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi =>
          sq_bound _ _ _ _ (hI (b i) (Finset.mem_image_of_mem b hi) g hg) (norm_nonneg _)
      rw [nsmul_eq_mul] at hTb
      have h2 := mul_le_mul_of_nonneg_left hTb hC₁
      nlinarith [h2, h13g]
    have h1 := hc (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) _ hA0 hcu hgu hdu
    calc _ ≤ _ := h1
      _ = _ := by rw [mul_pow, Real.sq_sqrt hKK]; ring
  have h5 := hB5 n ε V E hM ι b μ hb (evalAt 1 F) s _
    (mul_nonneg (Real.sqrt_nonneg _) hB) (fun R S hS => by simpa only [evalAt_apply] using key R S hS) hs v
  simpa only [evalAt_apply] using h5
end PositivityTheory.CW
