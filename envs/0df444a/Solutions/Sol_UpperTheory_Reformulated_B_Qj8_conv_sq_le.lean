-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qj8.conv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:02.909486+00:00
-- url     : https://prove2.me/submissions/b91e779b-c205-471b-be07-fce76794cda6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConvSqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qj8
theorem _root_.solution :
    ∀ {d : ℕ} (k g : UpperTheory.Reformulated.B.Qj8.E d → ENNReal),
      Measurable k →
        Measurable g →
          ∀ (ξ : UpperTheory.Reformulated.B.Qj8.E d),
            (∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η) ^ (2 : ℕ) ≤
              (∫⁻ (ζ : UpperTheory.Reformulated.B.Qj8.E d), k ζ) * ∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η ^ (2 : ℕ) := by
  intro d k g hk hg ξ
  have hk' : Measurable (fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η)) :=
    hk.comp (measurable_const.sub measurable_id)
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsq : ∀ a : ENNReal, (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq' : ∀ a : ENNReal, (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have H := ENNReal.lintegral_mul_norm_pow_le (μ := MeasureTheory.volume)
    (f := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η))
    (g := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η) * g η ^ (2 : ℕ))
    hk'.aemeasurable (hk'.mul (hg.pow_const 2)).aemeasurable hh hh (by norm_num)
  have hpt : ∀ η : UpperTheory.Reformulated.B.Qj8.E d,
      k (ξ - η) ^ (1 / 2 : ℝ) * (k (ξ - η) * g η ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = k (ξ - η) * g η := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh, hsq', ← mul_assoc, ← pow_two, hsq]
  simp only [hpt] at H
  rw [MeasureTheory.lintegral_sub_left_eq_self k ξ] at H
  calc _ ≤ _ := pow_le_pow_left₀ bot_le H 2
    _ = _ := by rw [mul_pow, hsq, hsq]
end UpperTheory.Reformulated.B.Qj8
