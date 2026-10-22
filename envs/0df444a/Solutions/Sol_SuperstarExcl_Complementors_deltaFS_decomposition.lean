-- Prove2me | solution 1 for SuperstarExcl.Complementors.deltaFS_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:36:16.951005+00:00
-- url     : https://prove2.me/submissions/6d8c23fa-4190-4c69-8b3d-d1919bf87561

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market
set_option autoImplicit false
open SuperstarExcl.Complementors

theorem solution (M : Model) (D₁ D₂ : ℝ) (hsum : D₁ + D₂ = 1)
    (hD₁ : 1 / 2 ≤ D₁) (hD₁' : D₁ ≤ 1) :
    FS M D₁ D₂ - ∫ k in (0)..(M.γ / 2), (M.γ - 2 * k) * M.lam k =
      0 * (∫ k in (0)..(M.γ * D₂), M.lam k) +
        (∫ k in (M.γ * D₂)..(M.γ / 2), (M.γ * (D₁ - 1) + k) * M.lam k) +
        ∫ k in (M.γ / 2)..(M.γ * D₁), (M.γ * D₁ - k) * M.lam k := by
  have hlam : M.lam = deriv M.Λ := funext fun k => (M.Λ_hasDerivAt k).deriv.symm
  have hc : Continuous M.lam := by
    rw [hlam]; exact M.Λ_contDiff.continuous_deriv (by norm_num)
  have hI : ∀ (g : ℝ → ℝ) (x y : ℝ), Continuous g → IntervalIntegrable (fun k => g k * M.lam k) MeasureTheory.volume x y :=
    fun g x y hg => (hg.mul hc).intervalIntegrable x y
  have hga : M.γ * (D₁ - 1) = -(M.γ * D₂) := by
    have : D₂ = 1 - D₁ := by linarith
    rw [this]; ring
  unfold FS
  set a := M.γ * D₂ with ha
  set b := M.γ * D₁ with hb
  have hab : a + b = M.γ := by rw [ha, hb, ← mul_add, add_comm, hsum, mul_one]
  have H1 : ∫ k in (0)..b, (b - k) * M.lam k =
      (∫ k in (0)..(M.γ / 2), (b - k) * M.lam k) + ∫ k in (M.γ / 2)..b, (b - k) * M.lam k :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hI (fun k => b - k) _ _ (by fun_prop)) (hI (fun k => b - k) _ _ (by fun_prop))).symm
  have H2 : ∫ k in (0)..(M.γ / 2), (a - k) * M.lam k =
      (∫ k in (0)..a, (a - k) * M.lam k) + ∫ k in a..(M.γ / 2), (a - k) * M.lam k :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hI (fun k => a - k) _ _ (by fun_prop)) (hI (fun k => a - k) _ _ (by fun_prop))).symm
  have H3 : ∫ k in (0)..(M.γ / 2), (M.γ - 2 * k) * M.lam k =
      (∫ k in (0)..(M.γ / 2), (b - k) * M.lam k) + ∫ k in (0)..(M.γ / 2), (a - k) * M.lam k := by
    rw [← intervalIntegral.integral_add (hI (fun k => b - k) _ _ (by fun_prop))
      (hI (fun k => a - k) _ _ (by fun_prop))]
    congr 1
    funext k
    rw [← hab]; ring
  have H4 : ∫ k in a..(M.γ / 2), (M.γ * (D₁ - 1) + k) * M.lam k =
      -∫ k in a..(M.γ / 2), (a - k) * M.lam k := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext k
    rw [hga]; ring
  rw [H4, zero_mul]
  linarith
