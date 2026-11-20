-- Prove2me | solution 1 for PhysReaudit.increment_mean
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:09:26.150227+00:00
-- url     : https://prove2.me/submissions/8450126a-bf1d-491f-9dc7-880f4398fb8a

import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_PhysReaudit_Delta

open LimitedPriceChanges.LowerBound PhysReaudit

theorem solution {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) :
    StrictAnti (fun q : ℝ => q * zMinus q₀ t + (1 - q) * zPlus q₀ t) ∧
    (∀ q ≤ q₀, q₀ * zMinus q₀ t + (1 - q₀) * zPlus q₀ t ≤ q * zMinus q₀ t + (1 - q) * zPlus q₀ t) ∧
    q₀ * zMinus q₀ t + (1 - q₀) * zPlus q₀ t = klBer q₀ t ∧
    0 < klBer q₀ t := by
  have ht : 0 < t := h0.trans h1
  have hzm : zMinus q₀ t < 0 := Real.log_neg (div_pos h0 ht) ((div_lt_one ht).mpr h1)
  have hzp : 0 < zPlus q₀ t :=
    Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
  have hanti : StrictAnti (fun q : ℝ => q * zMinus q₀ t + (1 - q) * zPlus q₀ t) := by
    intro x y hxy
    show y * zMinus q₀ t + (1 - y) * zPlus q₀ t < x * zMinus q₀ t + (1 - x) * zPlus q₀ t
    nlinarith
  refine ⟨hanti, fun q hq => hanti.antitone hq, rfl, ?_⟩
  -- strict Gibbs inequality
  have ha : Real.log (t / q₀) < t / q₀ - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos ht h0) (by
      intro h; rw [div_eq_one_iff_eq h0.ne'] at h; linarith)
  have hb : Real.log ((1 - t) / (1 - q₀)) ≤ (1 - t) / (1 - q₀) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  have e1 : Real.log (q₀ / t) = -Real.log (t / q₀) := by
    rw [← Real.log_inv, inv_div]
  have e2 : Real.log ((1 - q₀) / (1 - t)) = -Real.log ((1 - t) / (1 - q₀)) := by
    rw [← Real.log_inv, inv_div]
  have hq1 : 0 < 1 - q₀ := by linarith
  unfold klBer
  rw [e1, e2]
  have k1 : q₀ * (t / q₀ - 1) = t - q₀ := by field_simp
  have k2 : (1 - q₀) * ((1 - t) / (1 - q₀) - 1) = q₀ - t := by field_simp; ring
  nlinarith [mul_lt_mul_of_pos_left ha h0, mul_le_mul_of_nonneg_left hb hq1.le]
