-- Prove2me | solution 1 for SuperstarExcl.Complementors.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:01:53.606821+00:00
-- url     : https://prove2.me/submissions/bd3e9606-a1b4-4f23-bd64-9537ea228bd0

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market
import Theorems.Thm_SuperstarExcl_Complementors_lemma_2
import Theorems.Thm_SuperstarExcl_Complementors_lemma_3
import Theorems.Thm_SuperstarExcl_Complementors_deltaFS_decomposition

open SuperstarExcl.Complementors

theorem solution (M : Model) (ϕ : ℝ) (hϕ : 0 < ϕ) (p₁ p₂ D : ℝ → ℝ)
    (hpath : IsExclusivePath M ϕ p₁ p₂ D)
    (q E : ℝ) (hE : IsEquilibrium M ϕ 1 1 q q E) (hE₀ : 0 < E) (hE₁ : E < 1) :
    FS M E (1 - E) < FS M (D ϕ) (1 - D ϕ) := by
  -- Lemma 2: the non-exclusive split is equal
  have hEhalf : E = 1 / 2 := (lemma_2 M ϕ q E hE hE₀ hE₁).2.2.1
  -- Lemma 3: the favored platform has the larger share
  have h3 := (lemma_3 M ϕ hϕ p₁ p₂ D hpath).1
  have hmem : ϕ ∈ Set.Icc (0:ℝ) ϕ := ⟨hϕ.le, le_rfl⟩
  have hD1 : D ϕ < 1 := ((hpath.2.2.2.1 ϕ hmem).2.2)
  set d := D ϕ with hd
  have hdh : 1 / 2 < d := by linarith
  -- continuity of the density
  have hlam_cont : Continuous M.lam := by
    have h1 : deriv M.Λ = M.lam := funext fun k => (M.Λ_hasDerivAt k).deriv
    rw [← h1]
    exact M.Λ_contDiff.continuous_deriv (by norm_num)
  have hγ := M.γ_pos
  -- left side equals the reference integral
  have hL : FS M E (1 - E) = ∫ k in (0)..(M.γ / 2), (M.γ - 2 * k) * M.lam k := by
    rw [hEhalf, show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact FS_half M
  have hdec := deltaFS_decomposition M d (1 - d) (by ring) hdh.le hD1.le
  rw [hL]
  -- the switchers' term is nonnegative
  have hA : 0 ≤ ∫ k in (M.γ * (1 - d))..(M.γ / 2), (M.γ * (d - 1) + k) * M.lam k := by
    apply intervalIntegral.integral_nonneg
    · nlinarith
    · intro k hk
      have hk0 : 0 ≤ k := le_trans (by nlinarith) hk.1
      have hkγ : k ≤ M.γ := le_trans hk.2 (by linarith)
      have := M.lam_pos k ⟨hk0, hkγ⟩
      have : 0 ≤ M.γ * (d - 1) + k := by nlinarith [hk.1]
      positivity
  -- the entrants' term is positive
  have hB : 0 < ∫ k in (M.γ / 2)..(M.γ * d), (M.γ * d - k) * M.lam k := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact ((continuous_const.sub continuous_id).mul hlam_cont).intervalIntegrable _ _
    · intro k hk
      have hk0 : 0 ≤ k := le_trans (by linarith) hk.1.le
      have hkγ : k ≤ M.γ := le_trans hk.2.le (by nlinarith)
      have := M.lam_pos k ⟨hk0, hkγ⟩
      have : 0 < M.γ * d - k := by linarith [hk.2]
      positivity
    · nlinarith
  linarith
