-- Prove2me | solution 1 for PI.EF.exists_good_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:21.59953+00:00
-- url     : https://prove2.me/submissions/fffb59fd-c278-4cca-a103-dd7eb8c73f83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_exists_far_point
import Theorems.Thm_PI_EF_wsum_le
import Theorems.Thm_PI_EF_sum_mult_le_of_subset
import Theorems.Thm_PI_EF_card_le_sum_mult
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
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    ∃ T' ∈ Set.Icc T (T + 1), ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → LFunction χ ρ = 0 →
      1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤ |(|ρ.im|) - T'| := by
  have hf1 := (hC N χ hχ (T + 1 / 2)).1
  have hf2 := (hC N χ hχ (-(T + 1 / 2))).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlog : 0 ≤ Real.log (N * (T + 3)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hN1 (by linarith))
  have hK0 : 0 ≤ 2 * C * Real.log (N * (T + 3)) := mul_nonneg (mul_nonneg (by norm_num) hC0) hlog
  have hcardS : (((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) ≤
      2 * C * Real.log (N * (T + 3)) := by
    calc (((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)).card : ℝ)
        ≤ ((hf1.union hf2).toFinset.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ ∑ ρ ∈ (hf1.union hf2).toFinset, (mult χ ρ : ℝ) :=
          card_le_sum_mult χ _ (fun ρ hρ => by
            rw [Set.Finite.mem_toFinset] at hρ
            rcases hρ with h | h
            · exact ⟨h.2.1, h.2.2.2⟩
            · exact ⟨h.2.1, h.2.2.2⟩)
      _ ≤ wsum χ (T + 1 / 2) + wsum χ (-(T + 1 / 2)) :=
          sum_mult_le_of_subset χ hf1 hf2 _ (by
            intro x hx
            simpa using hx)
      _ ≤ C * Real.log (N * (T + 3)) + C * Real.log (N * (T + 3)) :=
          add_le_add
            (wsum_le hC0 hC χ hχ hT (by rw [abs_of_nonneg (by linarith)]; linarith))
            (wsum_le hC0 hC χ hχ hT (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith))
      _ = 2 * C * Real.log (N * (T + 3)) := by ring
  obtain ⟨x, hx, hfar⟩ := exists_far_point ((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)) T
  refine ⟨x, hx, fun ρ h0 h1 hL => ?_⟩
  have hmono : 1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤
      1 / (2 * ((((hf1.union hf2).toFinset.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  by_cases hw : |(|ρ.im|) - (T + 1 / 2)| ≤ 1
  · have hρB : ρ ∈ (hf1.union hf2).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact mem_window_of_abs χ h0 h1 hL hw
    have h3 := hfar (|ρ.im|) (Finset.mem_image_of_mem _ hρB)
    rw [abs_sub_comm] at h3
    linarith
  · push_neg at hw
    have hx' : |x - (T + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have htri := abs_sub_le (|ρ.im|) x (T + 1 / 2)
    have h3 : 1 / (2 * (2 * C * Real.log (N * (T + 3)) + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
end PI.EF
