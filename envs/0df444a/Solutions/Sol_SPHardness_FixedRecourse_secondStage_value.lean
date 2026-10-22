-- Prove2me | solution 1 for SPHardness.FixedRecourse.secondStage_value
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:39:17.921998+00:00
-- url     : https://prove2.me/submissions/cf7c1b77-9663-4075-b626-cd8e78f7a3a9

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model
set_option autoImplicit false
open MeasureTheory SPHardness.FixedRecourse

theorem solution {k : ℕ} (α : Fin k → ℝ)
    (β : ℝ)
    (hα : ∀ j, 0 ≤ α j) (ξ : Fin k → ℝ) (hξ : ξ ∈ cube k) :
    secondStageValue α β ξ = max ((∑ j, α j * ξ j) - β) 0 := by
  have hξ0 : ∀ j, 0 ≤ ξ j := fun j => (hξ j (Set.mem_univ j)).1
  unfold secondStageValue
  set c : ℝ := (∑ j, α j * ξ j) - β with hc
  apply IsGreatest.csSup_eq
  constructor
  · by_cases hc0 : 0 ≤ c
    · refine ⟨α, 1, hα, fun j => by simp, zero_le_one, le_rfl, ?_⟩
      rw [max_eq_left hc0, hc]
      simp only [mul_one]
      have : ∑ j, ξ j * α j = ∑ j, α j * ξ j := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      linarith
    · refine ⟨fun _ => 0, 0, fun _ => le_rfl, fun j => by simp, le_rfl, zero_le_one, ?_⟩
      rw [max_eq_right (not_le.1 hc0).le]
      simp
  · rintro v ⟨y, z, hy0, hyz, hz0, hz1, rfl⟩
    have h1 : ∑ j, ξ j * y j ≤ ∑ j, ξ j * (α j * z) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hyz j) (hξ0 j))
    have h2 : ∑ j, ξ j * (α j * z) = z * ∑ j, α j * ξ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have h3 : z * c ≤ max c 0 := by
      rcases le_total 0 c with h | h
      · calc z * c ≤ 1 * c := mul_le_mul_of_nonneg_right hz1 h
          _ = c := one_mul c
          _ ≤ max c 0 := le_max_left _ _
      · calc z * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz0 h
          _ ≤ max c 0 := le_max_right _ _
    rw [hc] at h3
    nlinarith
