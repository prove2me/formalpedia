-- Prove2me | solution 1 for PI.EF.trunc_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:53.590378+00:00
-- url     : https://prove2.me/submissions/f3bc1372-ed69-4d21-8efa-0ae31777749e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_wsum_le
import Theorems.Thm_PI_EF_sum_mult_le_of_subset
import Theorems.Thm_PI_EF_zerosBelow_finite
import Theorems.Thm_PI_EF_mem_window_of_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T T' u : ℝ} (hT : 0 < T)
    (hT' : T' ∈ Set.Icc T (T + 1)) (hu : 1 ≤ u) :
    ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
        ∑ᶠ ρ ∈ ZerosBelow χ T, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      2 * C * Real.log (N * (T + 3)) * (u / T) := by
  classical
  have hF' := zerosBelow_finite hC χ hχ T'
  have hF := zerosBelow_finite hC χ hχ T
  rw [finsum_mem_eq_finite_toFinset_sum _ hF', finsum_mem_eq_finite_toFinset_sum _ hF]
  have hsub : hF.toFinset ⊆ hF'.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨a, b, c, d⟩ := hρ
    exact ⟨a, b, lt_of_lt_of_le c hT'.1, d⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hD : ∀ ρ ∈ hF'.toFinset \ hF.toFinset, 0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ |ρ.im| ∧
      |ρ.im| ≤ T + 1 ∧ LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨a, b, c, d⟩, hn⟩ := hρ
    refine ⟨a, b, ?_, by linarith [hT'.2], d⟩
    by_contra hlt
    push_neg at hlt
    exact hn ⟨a, b, hlt, d⟩
  have hsumm : ∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ) ≤
      2 * C * Real.log (N * (T + 3)) := by
    have hf1 := (hC N χ hχ (T + 1 / 2)).1
    have hf2 := (hC N χ hχ (-(T + 1 / 2))).1
    calc ∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ)
        ≤ wsum χ (T + 1 / 2) + wsum χ (-(T + 1 / 2)) :=
          sum_mult_le_of_subset χ hf1 hf2 _ (fun ρ hρ => by
            obtain ⟨a, b, c, d, e⟩ := hD ρ hρ
            exact mem_window_of_abs χ a b e (by rw [abs_le]; constructor <;> linarith))
      _ ≤ C * Real.log (N * (T + 3)) + C * Real.log (N * (T + 3)) :=
          add_le_add
            (wsum_le hC0 hC χ hχ hT.le (by rw [abs_of_pos (by linarith)]; linarith))
            (wsum_le hC0 hC χ hχ hT.le (by rw [abs_neg, abs_of_pos (by linarith)]; linarith))
      _ = 2 * C * Real.log (N * (T + 3)) := by ring
  have hu0 : (0 : ℝ) < u := by linarith
  have hterm : ∀ ρ ∈ hF'.toFinset \ hF.toFinset,
      ‖(mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (mult χ ρ : ℝ) * (u / T) := by
    intro ρ hρ
    obtain ⟨a, b, c, d, e⟩ := hD ρ hρ
    have hρn : T ≤ ‖ρ‖ := c.trans (Complex.abs_im_le_norm ρ)
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply div_le_div₀ hu0.le _ hT hρn
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu b.le
      _ = u := Real.rpow_one u
  calc ‖∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖
      ≤ ∑ ρ ∈ hF'.toFinset \ hF.toFinset, ‖(mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ) * (u / T) := Finset.sum_le_sum hterm
    _ = (∑ ρ ∈ hF'.toFinset \ hF.toFinset, (mult χ ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]
    _ ≤ 2 * C * Real.log (N * (T + 3)) * (u / T) :=
        mul_le_mul_of_nonneg_right hsumm (div_nonneg hu0.le hT.le)
end PI.EF
