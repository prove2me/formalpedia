-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsFil.exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:16.857791+00:00
-- url     : https://prove2.me/submissions/4a1060d9-82c8-4f7d-918c-3837fb134b93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace IsFil
theorem _root_.solution (hF : IsFil F L) {x : A} (hx : x ∈ F 0) :
    ‖NormedSpace.exp x - 1‖ ≤ ((L : ℝ) + 1) * ‖x‖ * (1 + ‖x‖) ^ L := by
  have hE : NormedSpace.exp x - 1 =
      x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) := by
    rw [hF.exp_eq hx]
    abel
  rw [hE]
  have ht : 0 ≤ ‖x‖ := norm_nonneg _
  have hp : 1 ≤ 1 + ‖x‖ := by linarith
  have hPL : 1 ≤ (1 + ‖x‖) ^ L := one_le_pow₀ hp
  have hterm : ∀ k ∈ Finset.range L,
      ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ ≤ ‖x‖ * (1 + ‖x‖) ^ L := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [norm_smul]
    have hc : ‖(((k + 2).factorial : ℝ)⁻¹)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _))
    have hxk : ‖x ^ (k + 2)‖ ≤ ‖x‖ ^ (k + 2) := norm_pow_le' x (by omega)
    have hk2 : ‖x‖ ^ (k + 2) ≤ ‖x‖ * (1 + ‖x‖) ^ L := by
      have e : ‖x‖ ^ (k + 2) = ‖x‖ * ‖x‖ ^ (k + 1) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ ht
      calc ‖x‖ ^ (k + 1) ≤ (1 + ‖x‖) ^ (k + 1) := pow_le_pow_left₀ ht (by linarith) _
        _ ≤ (1 + ‖x‖) ^ L := pow_le_pow_right₀ hp (by omega)
    calc ‖(((k + 2).factorial : ℝ)⁻¹)‖ * ‖x ^ (k + 2)‖ ≤ 1 * ‖x ^ (k + 2)‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ ‖x‖ * (1 + ‖x‖) ^ L := by rw [one_mul]; exact hxk.trans hk2
  have hsum : ‖∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ ≤
      L * (‖x‖ * (1 + ‖x‖) ^ L) := by
    calc _ ≤ ∑ k ∈ Finset.range L, ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range L, ‖x‖ * (1 + ‖x‖) ^ L := Finset.sum_le_sum hterm
      _ = L * (‖x‖ * (1 + ‖x‖) ^ L) := by simp
  have hx1 : ‖x‖ ≤ ‖x‖ * (1 + ‖x‖) ^ L := le_mul_of_one_le_right ht hPL
  refine (norm_add_le _ _).trans ?_
  nlinarith [hsum, hx1]
end IsFil
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
