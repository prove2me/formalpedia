-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.contDiff_comp_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:30.091009+00:00
-- url     : https://prove2.me/submissions/196010d5-786f-4657-ba45-f9f78e4838d0

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_hasFDerivAt_of_partials
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_continuous_pr
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_exists_partial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.UMGS
open Filter Topology Function
variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKEst.UMGS
theorem _root_.solution [FiniteDimensional ℝ A] (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G))
    (hc : ∀ γ ∈ L, Continuous γ) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L) (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y)
    {r : ℕ} (β : Fin r → (Multiplicative ℝ →* G)) (c : Fin r → (ι → A) →ₗ[ℝ] ℝ) (hβ : ∀ j, β j ∈ L)
    (hl : ∀ (f : G → ℂ) (f' : Fin r → G → ℂ), (∀ j, Continuous (f' j) ∧
      ∀ h, HasDerivAt (fun t : ℝ => f (h * β j (Multiplicative.ofAdd t))) (f' j h) 0) → ∀ γ ∈ L, ∀ Y, Gn m γ Y →
      ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ j, (c j Y : ℂ) * f' j h) 0)
    (S : Set (G → ℂ)) (hS : ∀ f ∈ S, Continuous f ∧
      ∀ γ ∈ L, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0)
    {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (hγ : ∀ i, γ i ∈ L) (g : G) (n : ℕ) :
    ∀ f ∈ S, ContDiff ℝ n fun t => f (g * pr γ t) := by
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 ((hS f hf).1.comp (continuous_const.mul (continuous_pr k γ fun i => hc _ (hγ i))))
  | succ n ih =>
    intro f hf
    choose f' hf'S hf' using fun j => (hS f hf).2 _ (hβ j)
    choose Z hZ hZ' using exists_partial m L hcj hg n k γ hγ
    have hD : ∀ i, ContDiff ℝ n fun t => ∑ j, (c j (Z i t) : ℂ) * f' j (g * pr γ t) := fun i =>
      ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp
        ((LinearMap.toContinuousLinearMap (c j)).contDiff.comp (hZ i))).mul (ih _ (hf'S j))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, hasFDerivAt_of_partials k _ _ (fun i => (hD i).continuous) fun i t => ?_⟩
    · exact ContDiff.sum fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hD i)
    · obtain ⟨γ', h1, h2, h3⟩ := hZ' i t
      simp only [h3, ← mul_assoc]
      exact hl f f' (fun j => ⟨(hS _ (hf'S j)).1, hf' j⟩) γ' h1 _ h2 _
end PositivityTheory.ThKEst.UMGS
