-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.of_eventually_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:35.7493+00:00
-- url     : https://prove2.me/submissions/c8668c0f-e03b-4d1a-a489-02f86c2424cf

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_Dominated_trans


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ (a + η)) : IsPowLittleO f a := by
  -- All three claims are about `n ≥ 2`, where `n > 1` and the maximum is positive.
  have hbase : ∀ n : ℕ, 2 ≤ n → (1 : ℝ) < n ∧ 0 < max |f n| ((n : ℝ) ^ a) := fun n hn =>
    ⟨by exact_mod_cast hn, lt_max_of_lt_right (Real.rpow_pos_of_pos (by positivity) a)⟩
  refine ⟨fun n => Real.logb n (max |f n| ((n : ℝ) ^ a)) - a,
    tendsto_order.2 ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩, ?_⟩
  · -- `ε(n) ≥ 0`, because the maximum is at least `n^a`.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hge : a ≤ Real.logb n (max |f n| ((n : ℝ) ^ a)) :=
      (Real.le_logb_iff_rpow_le hn1 hpos).2 (le_max_right _ _)
    linarith [hδ, hge]
  · -- `ε(n) ≤ δ/2` as soon as `|f(n)| ≤ n^{a+δ/2}`.
    filter_upwards [h (δ / 2) (half_pos hδ), eventually_ge_atTop 2] with n hfn hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hle : Real.logb n (max |f n| ((n : ℝ) ^ a)) ≤ a + δ / 2 :=
      (Real.logb_le_iff_le_rpow hn1 hpos).2
        (max_le hfn (Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)))
    linarith [hδ, hle]
  · -- `n^{a+ε(n)}` is the maximum.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    rw [add_sub_cancel, Real.rpow_logb (zero_lt_one.trans hn1) hn1.ne' hpos]
    exact le_max_left _ _
end IsPowLittleO
end ThreeSumApsp
