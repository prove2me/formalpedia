-- Prove2me | solution 1 for SuperstarExcl.Complementors.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:11:04.818995+00:00
-- url     : https://prove2.me/submissions/214199de-6aa5-48f0-bed3-9832ab47e504

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market
import Theorems.Thm_SuperstarExcl_Complementors_lemma_3

open SuperstarExcl.Complementors Set

theorem solution (M : Model) (ϕ : ℝ) (hϕ : 0 < ϕ) (p₁ p₂ D : ℝ → ℝ)
    (hpath : IsExclusivePath M ϕ p₁ p₂ D) :
    (∀ k, 0 < k → k ≤ M.γ * (1 - D ϕ) → Multihomes M (D ϕ) (1 - D ϕ) k) ∧
      (∀ k, M.γ * (1 - D ϕ) < k → k ≤ M.γ * D ϕ → SinglehomesOn1 M (D ϕ) (1 - D ϕ) k) ∧
      (∀ k, M.γ * D ϕ < k → Zerohomes M (D ϕ) (1 - D ϕ) k) ∧
      M.Λ (M.γ / 2) < M.Λ (M.γ * D ϕ) ∧
      M.γ * (1 - D ϕ) < M.γ * D ϕ := by
  have hmem : ϕ ∈ Icc (0:ℝ) ϕ := ⟨hϕ.le, le_rfl⟩
  have hD₁ : D ϕ < 1 := (hpath.2.2.2.1 ϕ hmem).2.2
  have h3 := (lemma_3 M ϕ hϕ p₁ p₂ D hpath).1
  have hγ := M.γ_pos
  have hΛmono : StrictMonoOn M.Λ (Icc 0 M.γ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact M.Λ_contDiff.continuous.continuousOn
    · intro k hk
      rw [interior_Icc] at hk
      rw [(M.Λ_hasDerivAt k).deriv]
      exact M.lam_pos k (Ioo_subset_Icc_self hk)
  have hlt : M.γ * (1 - D ϕ) < M.γ * D ϕ := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, hlt⟩
  · intro k _ hk
    exact ⟨le_trans hk hlt.le, hk⟩
  · intro k hk1 hk2
    exact ⟨hk2, not_le.mpr hk1⟩
  · intro k hk
    exact ⟨not_le.mpr hk, not_le.mpr (lt_trans hlt hk)⟩
  · apply hΛmono ⟨by linarith, by linarith⟩ ⟨by nlinarith, by nlinarith⟩
    nlinarith
