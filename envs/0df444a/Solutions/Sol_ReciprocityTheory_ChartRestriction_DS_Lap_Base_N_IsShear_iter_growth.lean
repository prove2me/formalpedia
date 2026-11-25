-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.iter_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:48.503091+00:00
-- url     : https://prove2.me/submissions/adfefed8-799c-46d1-82eb-6e4db89b1f32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_iter_mem

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
namespace IsShear
theorem _root_.solution (hf : IsShear F f) {Cf : ℝ} {Mf : ℕ} (hCf : 0 ≤ Cf)
    (hb : ∀ x ∈ F 0, ‖f x‖ ≤ Cf * ‖x‖ * (1 + ‖x‖) ^ Mf) (i : ℕ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ z ∈ F 0, ‖iter f i z‖ ≤ C * ‖z‖ * (1 + ‖z‖) ^ M := by
  induction i with
  | zero =>
    refine ⟨0, 0, le_refl 0, fun z _ => ?_⟩
    show ‖(0 : A)‖ ≤ 0 * ‖z‖ * (1 + ‖z‖) ^ 0
    simp
  | succ i ih =>
    obtain ⟨C, M, hC, hbd⟩ := ih
    have hK : 0 ≤ Cf * C * (1 + C) ^ Mf :=
      mul_nonneg (mul_nonneg hCf hC) (pow_nonneg (by linarith) Mf)
    refine ⟨C + 1 + Cf * C * (1 + C) ^ Mf, M + (M + 1) * Mf, by linarith, fun z hz => ?_⟩
    have hw0 : iter f i z ∈ F 0 := (IsShear.iter_mem hf hz i).1
    have hw : ‖iter f i z‖ ≤ C * ‖z‖ * (1 + ‖z‖) ^ M := hbd z hz
    have hfw : ‖f (iter f i z)‖ ≤ Cf * ‖iter f i z‖ * (1 + ‖iter f i z‖) ^ Mf := hb _ hw0
    have ht : 0 ≤ ‖z‖ := norm_nonneg _
    have hp : 1 ≤ 1 + ‖z‖ := by linarith
    have hQ1 : 1 ≤ (1 + ‖z‖) ^ (M + 1) := one_le_pow₀ hp
    have hR : 1 ≤ (1 + ‖z‖) ^ ((M + 1) * Mf) := one_le_pow₀ hp
    have hQ : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ hp
    have hwp : ‖iter f i z‖ ≤ C * (1 + ‖z‖) ^ (M + 1) := by
      have e : C * (1 + ‖z‖) ^ (M + 1) = C * (1 + ‖z‖) * (1 + ‖z‖) ^ M := by ring
      rw [e]
      exact hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC)
        (by positivity))
    have h1w : 1 + ‖iter f i z‖ ≤ (1 + C) * (1 + ‖z‖) ^ (M + 1) := by nlinarith
    have hpow : (1 + ‖iter f i z‖) ^ Mf ≤ (1 + C) ^ Mf * (1 + ‖z‖) ^ ((M + 1) * Mf) := by
      rw [pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1w Mf
    have hfw2 : ‖f (iter f i z)‖ ≤
        Cf * (C * ‖z‖ * (1 + ‖z‖) ^ M) * ((1 + C) ^ Mf * (1 + ‖z‖) ^ ((M + 1) * Mf)) :=
      hfw.trans (mul_le_mul (mul_le_mul_of_nonneg_left hw hCf) hpow (by positivity)
        (mul_nonneg hCf (mul_nonneg (mul_nonneg hC ht) (by positivity))))
    have hsum : ‖iter f (i + 1) z‖ ≤ ‖iter f i z‖ + (‖z‖ + ‖f (iter f i z)‖) := by
      show ‖iter f i z + (z - f (iter f i z))‖ ≤ _
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    have e1 : C * ‖z‖ * (1 + ‖z‖) ^ M ≤ C * ‖z‖ * (1 + ‖z‖) ^ M * (1 + ‖z‖) ^ ((M + 1) * Mf) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg hC ht) (by positivity)) hR
    have e2 : ‖z‖ ≤ ‖z‖ * ((1 + ‖z‖) ^ M * (1 + ‖z‖) ^ ((M + 1) * Mf)) :=
      le_mul_of_one_le_right ht (one_le_mul_of_one_le_of_one_le hQ hR)
    rw [pow_add]
    nlinarith [hsum, hw, hfw2, e1, e2]
end IsShear
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
