-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_likelihood_mean_small
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:38:41.328922+00:00
-- url     : https://prove2.me/submissions/d4aa57a2-8838-4d91-a457-e7a455be54a1

import Theorems.Thm_ZeroFreeRRG_Hardcore_unique_maximum_small_perturbation
import Mathlib
set_option autoImplicit false
open Set ZeroFreeRRG.Hardcore

theorem solution {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0)
    (E : ℝ → ℕ → ℝ)
    (hbound : ∀ s : ℝ, 0 < s → s < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∃ x ∈ K, E s n ≤ f x + s*g x + δ) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, E s n ≤ ε*s := by
  intro ε hε
  obtain ⟨s₀,hs₀,huni⟩ := unique_maximum_small_perturbation K hK f g hf hg x₀ hx₀
    hfnonpos hfzero hunique hgzero (ε/2) (by linarith)
  let s := min s₀ 1 / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by dsimp [s]; have h := min_le_right s₀ (1:ℝ); linarith
  have hs0 : s < s₀ := by dsimp [s]; have h := min_le_left s₀ (1:ℝ); linarith
  obtain ⟨N,hN⟩ := hbound s hs hs1 (ε*s/2) (by positivity)
  refine ⟨s,hs,hs1,N,?_⟩
  intro n hn
  obtain ⟨x,hx,hxE⟩ := hN n hn
  have hxuni := huni s hs hs0 x hx
  nlinarith
