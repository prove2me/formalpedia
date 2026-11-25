-- Prove2me | solution 1 for ReciprocityTheory.Cheb.gs_diff_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:23:04.807912+00:00
-- url     : https://prove2.me/submissions/fad9ed22-9013-4662-b843-4be9e919dd6c

import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Theorems.Thm_ReciprocityTheory_Cheb_core_const_eq
import Theorems.Thm_ReciprocityTheory_Cheb_rpow_neg_finrank_sub_one
import Theorems.Thm_ReciprocityTheory_Cheb_Gs_of_uphi_eq_zero
import Theorems.Thm_ReciprocityTheory_Cheb_exists_support_bound
import Theorems.Thm_ReciprocityTheory_Cheb_exists_ucoord_bound
import Theorems.Thm_ReciprocityTheory_Cheb_norm_Gs_add_sub_le_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (B : ℝ) :
    ∃ R₀ C : ℝ, ∀ s ∈ Set.Icc (1 : ℝ) 2, ∀ x h : mixedSpace E, ‖h‖ ≤ B → R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + h) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by
  obtain ⟨c₀, hc₀, -, hsupp⟩ := exists_support_bound (E := E)
  obtain ⟨A, hA, hAb⟩ := exists_ucoord_bound (E := E)
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := by linarith
  set n := Module.finrank ℚ E with hn
  set R₁ := (2 * B' + 2) / c₀ with hR₁
  have hR₁0 : 0 < R₁ := div_pos (by linarith) hc₀
  set K := (8 * A * B' + 4 * (n : ℝ) * B') / c₀ * (2 / c₀) ^ n with hK
  have hK0 : 0 ≤ K := by positivity

  have core : ∀ s ∈ Set.Icc (1 : ℝ) 2, ∀ y k : mixedSpace E, uphi y ≠ 0 → ‖k‖ ≤ B' → R₁ ≤ ‖y‖ →
      ‖Gs χ s (y + k) - Gs χ s y‖ ≤ K * (‖y‖ ^ (n + 1))⁻¹ := by
    intro s hs y k hyu hk hy
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR₁0 hy
    have hcy : 2 * B' + 2 ≤ c₀ * ‖y‖ := by
      rw [hR₁, div_le_iff₀ hc₀] at hy; linarith
    have h := norm_Gs_add_sub_le_core χ hs hA hAb hB'0 hk (a := c₀ * ‖y‖) (by linarith) (by linarith)
      (hsupp y hyu).1
    rwa [core_const_eq n hc₀ hy0] at h
  refine ⟨2 * R₁ + 2 * B', K * 2 ^ (n + 1), fun s hs x h hh hx => ?_⟩
  have hx0 : 0 < ‖x‖ := by linarith
  have hhB : ‖h‖ ≤ B' := hh.trans (le_max_left _ _)
  rw [rpow_neg_finrank_sub_one _ (norm_nonneg _) n]
  have hpow : 0 < ‖x‖ ^ (n + 1) := pow_pos hx0 _
  by_cases h1 : uphi x ≠ 0
  · refine (core s hs x h h1 hhB (by linarith)).trans ?_
    have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    calc K * (‖x‖ ^ (n + 1))⁻¹ = K * (‖x‖ ^ (n + 1))⁻¹ * 1 := by ring
      _ ≤ K * (‖x‖ ^ (n + 1))⁻¹ * 2 ^ (n + 1) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hK0 (inv_pos.mpr hpow).le)
      _ = K * 2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ := by ring
  by_cases h2 : uphi (x + h) ≠ 0
  · have hy : ‖x‖ / 2 ≤ ‖x + h‖ := by
      have := norm_sub_norm_le x (-h)
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    have hc := core s hs (x + h) (-h) h2 (by rwa [norm_neg]) (by linarith)
    rw [add_neg_cancel_right, norm_sub_rev] at hc
    refine hc.trans ?_
    have hxy : (‖x + h‖ ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ := by
      have e : (2 : ℝ) ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ = ((‖x‖ / 2) ^ (n + 1))⁻¹ := by
        rw [div_pow]; field_simp
      rw [e]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hy _)
    calc K * (‖x + h‖ ^ (n + 1))⁻¹ ≤ K * (2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left hxy hK0
      _ = K * 2 ^ (n + 1) * (‖x‖ ^ (n + 1))⁻¹ := by ring
  push Not at h1 h2
  rw [Gs_of_uphi_eq_zero χ s h1, Gs_of_uphi_eq_zero χ s h2, sub_zero, norm_zero]
  positivity
end ReciprocityTheory.Cheb
