-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:28:51.818435+00:00
-- url     : https://prove2.me/submissions/c504b8c7-8e18-408b-af8c-31c2117be7ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paU_norm_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPoly_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution {q c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v : EuclideanSpace ℂ ι, ‖paU q a F v‖ ≤
      C * (1 + ‖v‖) ^ c * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) *
        ((1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
  obtain ⟨C1, hC1, h1⟩ := paPoly_growth hF
  refine ⟨C1, hC1, fun a v => ?_⟩
  have hn := paU_norm_mul q a v F
  have hW : paW q v * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) = 1 := by
    rw [paW, ← Real.exp_add]; simp
  have hE1 : Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (q : ℝ) * Real.pi := by positivity
    nlinarith [sq_nonneg ‖v - (1 / 2 : ℂ) • a‖]
  have hva : 1 + ‖v - a‖ ≤ (1 + ‖v‖) * (1 + ‖a‖) := by
    nlinarith [norm_sub_le v a, norm_nonneg v, norm_nonneg a, mul_nonneg (norm_nonneg v) (norm_nonneg a)]
  have ha : (1 + ‖a‖) ^ c ≤ (1 + ‖a‖) ^ (2 * c) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg a]) (by omega)
  have E2 := Real.exp_pos (-(q * Real.pi) * ‖a‖ ^ 2 / 4)
  have EV := Real.exp_pos ((q * Real.pi) * ‖v‖ ^ 2)
  have hU : ‖paU q a F v‖ = (‖paU q a F v‖ * paW q v) * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by
    rw [mul_assoc, hW, mul_one]
  rw [hU, hn]
  have k1 : ‖F (v - a)‖ ≤ C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c)) := by
    refine (h1 _).trans (mul_le_mul_of_nonneg_left ?_ hC1)
    calc (1 + ‖v - a‖) ^ c ≤ ((1 + ‖v‖) * (1 + ‖a‖)) ^ c :=
          pow_le_pow_left₀ (by linarith [norm_nonneg (v - a)]) hva c
      _ = (1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c := mul_pow _ _ _
      _ ≤ (1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c) :=
          mul_le_mul_of_nonneg_left ha (by positivity)
  have hFn := norm_nonneg (F (v - a))
  have hE1p := Real.exp_pos (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2)
  calc ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) *
        Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) * Real.exp ((q * Real.pi) * ‖v‖ ^ 2)
      ≤ ‖F (v - a)‖ * (1 * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) *
          Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by gcongr
    _ ≤ C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c)) * (1 * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) *
          Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by gcongr
    _ = _ := by ring
end ReciprocityTheory.ChartRestriction.G.I2.FPw
