-- Prove2me | solution 1 for UpperTheory.Reformulated.B.LiftErrorLocal.shell_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:38.466918+00:00
-- url     : https://prove2.me/submissions/068349b1-a526-4e0a-9af1-1a6bf3e4103c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.LiftErrorLocal
theorem _root_.solution :
    UpperTheory.Reformulated.B.LiftErrorLocal.ShellInt := by
  intro X _ μ N C d A hN h1 hd hμ hA
  have hA0 : -A ≤ 0 := by linarith
  have hmeas : ∀ k : ℕ, MeasurableSet {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} := fun k =>
    measurableSet_le hN measurable_const
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤
      ∑' k : ℕ, {x : X | N x ≤ (2 : ℝ) ^ (k + 1)}.indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem (show x ∈ {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} from hk2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hk1 hA0)
  have hr : (2 : ℝ) ^ (d - A) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (d - A) := by positivity
  have hsum : Summable fun k : ℕ => C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (-A) * (C * ((2 : ℝ) ^ (k + 1)) ^ d) =
      C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k := by
    intro k
    have h2 : (0 : ℝ) < 2 := two_pos
    have hk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [pow_succ, Real.mul_rpow hk.le h2.le, Real.rpow_pow_comm h2.le, sub_eq_add_neg,
      Real.rpow_add hk]
    ring
  calc ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ
      ≤ ∫⁻ x, ∑' k : ℕ, {x : X | N x ≤ (2 : ℝ) ^ (k + 1)}.indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A))) x ∂μ :=
        MeasureTheory.lintegral_mono_ae hpt
    _ = ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A)) *
        μ {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} := by
        rw [MeasureTheory.lintegral_tsum
          (fun k => (measurable_const.indicator (hmeas k)).aemeasurable)]
        exact tsum_congr fun k => MeasureTheory.lintegral_indicator_const (hmeas k) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [← hterm k, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hμ _ (one_le_pow₀ one_le_two)
    _ < ⊤ := hsum.tsum_ofReal_lt_top
end UpperTheory.Reformulated.B.LiftErrorLocal
