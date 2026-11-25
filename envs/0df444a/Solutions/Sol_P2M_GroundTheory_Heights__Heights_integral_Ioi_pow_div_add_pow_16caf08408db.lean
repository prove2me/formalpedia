-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integral_Ioi_pow_div_add_pow_16caf08408db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:36.416588+00:00
-- url     : https://prove2.me/submissions/62b9bba9-aa80-46bf-be08-5473be593728

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FubiniStudyIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set Filter Topology Real
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : ℝ) (hc : 0 < c) (k : ℕ) : ∀ b : ℕ,
    IntegrableOn (fun t : ℝ => t ^ b / (c + t) ^ (b + 2 + k)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), t ^ b / (c + t) ^ (b + 2 + k) =
      ((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1) := by
  intro b
  induction b with
  | zero =>
    have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1))))
        ((fun t : ℝ => t ^ 0 / (c + t) ^ (0 + 2 + k)) x) x := by
      intro x hx
      have hx' : 0 < c + x := by have := mem_Ici.mp hx; linarith
      have h1 : HasDerivAt (fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1))
          ((k + 1 : ℝ) * ((k + 1 : ℕ) * (c + x) ^ k * 1)) x := by
        exact ((((hasDerivAt_id x).const_add c).pow (k + 1))).const_mul _
      have h2 := (h1.inv (by positivity)).neg
      have hfun : (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) =
          -(fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1))⁻¹ := by
        funext t; simp [one_div]
      rw [hfun]
      refine h2.congr_deriv ?_
      have hne : (c + x) ≠ 0 := hx'.ne'
      simp only [pow_zero]
      field_simp
      push_cast
      ring
    have hpos : ∀ x ∈ Ioi (0:ℝ), 0 ≤ (fun t : ℝ => t ^ 0 / (c + t) ^ (0 + 2 + k)) x := by
      intro x hx
      have : 0 < c + x := by have := mem_Ioi.mp hx; linarith
      positivity
    have hlim : Tendsto (fun t : ℝ => -(1 / ((k + 1 : ℝ) * (c + t) ^ (k + 1)))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => (k + 1 : ℝ) * (c + t) ^ (k + 1)) atTop atTop := by
        refine Tendsto.const_mul_atTop (by positivity) ?_
        exact (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ c tendsto_id)
      have := (tendsto_inv_atTop_zero.comp h0).neg
      simpa [one_div] using this
    refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
    simp only [Nat.factorial_zero, one_mul, zero_add, add_zero]
    have hk : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
      push_cast [Nat.factorial_succ]; ring
    rw [hk]
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  | succ b ih =>
    obtain ⟨hint, hval⟩ := ih
    have hint' : IntegrableOn (fun t : ℝ => t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k)) (Ioi 0) := by
      refine hint.mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro x hx
        have : 0 < c + x := by have := mem_Ioi.mp hx; linarith
        exact ((continuous_pow _).continuousAt.div (by fun_prop) (by positivity)).continuousWithinAt
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx0 : 0 < x := hx
        have hcx : 0 < c + x := by linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 : (c + x) ^ (b + 1 + 2 + k) = (c + x) ^ (b + 2 + k) * (c + x) := by ring
        rw [e1, pow_succ]
        have := mul_le_mul_of_nonneg_left (show x ≤ c + x by linarith)
            (show 0 ≤ x ^ b * (c + x) ^ (b + 2 + k) by positivity)
        nlinarith
    refine ⟨hint', ?_⟩
    set G : ℝ → ℝ := fun t => t ^ (b + 1) / (c + t) ^ (b + 2 + k) with hG
    set G' : ℝ → ℝ := fun t => (b + 1 : ℝ) * (t ^ b / (c + t) ^ (b + 2 + k)) -
      (b + 2 + k : ℝ) * (t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k)) with hG'
    have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt G (G' x) x := by
      intro x hx
      have hcx : 0 < c + x := by have := mem_Ici.mp hx; linarith
      have h0 : HasDerivAt (fun t : ℝ => c + t) 1 x := (hasDerivAt_id x).const_add c
      have h1 : HasDerivAt G (((b + 1 : ℕ) * x ^ b * (c + x) ^ (b + 2 + k) -
          x ^ (b + 1) * ((b + 2 + k : ℕ) * (c + x) ^ (b + 2 + k - 1) * 1)) /
          ((c + x) ^ (b + 2 + k)) ^ 2) x :=
        (hasDerivAt_pow (b + 1) x).div (h0.pow (b + 2 + k)) (pow_pos hcx _).ne'
      refine h1.congr_deriv ?_
      simp only [hG']
      have hne : (c + x) ≠ 0 := hcx.ne'
      rw [show b + 2 + k - 1 = b + 1 + k by omega]
      field_simp
      push_cast
      ring
    have hG'int : IntegrableOn G' (Ioi 0) :=
      (hint.const_mul _).sub (hint'.const_mul _)
    have hlim : Tendsto G atTop (𝓝 0) := by
      have hup : Tendsto (fun t : ℝ => 1 / (c + t) ^ (k + 1)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun t : ℝ => (c + t) ^ (k + 1)) atTop atTop :=
          (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ c tendsto_id)
        simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with t ht
        have : 0 < c + t := by linarith
        positivity
      · filter_upwards [eventually_ge_atTop 0] with t ht
        have hct : 0 < c + t := by linarith
        simp only [hG]
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        have h1 : t ^ (b + 1) ≤ (c + t) ^ (b + 1) := pow_le_pow_left₀ ht (by linarith) _
        have h2 : (c + t) ^ (b + 1) * (c + t) ^ (k + 1) = (c + t) ^ (b + 2 + k) := by
          rw [← pow_add]; congr 1; omega
        rw [← h2]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hG'int hlim
    simp only [hG, hG'] at key
    rw [integral_sub (hint.const_mul _) (hint'.const_mul _), integral_const_mul,
      integral_const_mul, hval] at key
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, sub_zero] at key
    have hb2 : (b + 2 + k : ℝ) ≠ 0 := by positivity
    have e : ∫ t in Ioi (0:ℝ), t ^ (b + 1) / (c + t) ^ (b + 1 + 2 + k) =
        (b + 1 : ℝ) * (((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1))
          / (b + 2 + k) := by
      rw [eq_div_iff hb2]; linear_combination -key
    rw [e]
    have hf : ((b + 1 + k + 1).factorial : ℝ) = (b + k + 2) * (b + k + 1).factorial := by
      rw [show b + 1 + k + 1 = (b + k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [hf, show (b + 1).factorial = (b + 1) * b.factorial from Nat.factorial_succ b]
    push_cast
    have : ((b + k + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
end GroundTheory.Heights₂.Heights
