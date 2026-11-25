-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.eq_zero_of_ev_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:23.355852+00:00
-- url     : https://prove2.me/submissions/13229657-7928-4454-bc9e-29feebf989d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_hasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
private theorem eq_zero_at_zero_of_tsum_mul_pow_eq_zero (b : ℕ → ℂ) (hb : Summable fun i => ‖b i‖ * (1 / 2 : ℝ) ^ i)
    (h0 : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∑' i, b i * (t : ℂ) ^ i = 0) : b 0 = 0 := by
  have hK : Summable fun i => ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i := by
    refine (((summable_nat_add_iff 1).mpr hb).mul_left 2).congr fun i => ?_
    beta_reduce
    ring
  have hmain : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ‖b 0‖ ≤ t * ∑' i, ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i := by
    intro t ht hle
    have hbd : ∀ i, ‖b i * (t : ℂ) ^ i‖ ≤ ‖b i‖ * (1 / 2 : ℝ) ^ i := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hle i) (norm_nonneg _)
    have hGn : Summable fun i => ‖b i * (t : ℂ) ^ i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hb
    have hG : Summable fun i => b i * (t : ℂ) ^ i := hGn.of_norm
    have hsplit := hG.tsum_eq_zero_add
    rw [h0 t ht hle, pow_zero, mul_one] at hsplit
    have hb0 : b 0 = -∑' i, b (i + 1) * (t : ℂ) ^ (i + 1) := by linear_combination -hsplit
    have hGn1 : Summable fun i => ‖b (i + 1) * (t : ℂ) ^ (i + 1)‖ :=
      (summable_nat_add_iff 1).mpr hGn
    have hle2 : ∀ i, ‖b (i + 1) * (t : ℂ) ^ (i + 1)‖ ≤ t * (‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, pow_succ]
      calc ‖b (i + 1)‖ * (t ^ i * t) = t * (‖b (i + 1)‖ * t ^ i) := by ring
        _ ≤ t * (‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hle i) (norm_nonneg _)) ht.le
    rw [hb0, norm_neg]
    exact (norm_tsum_le_tsum_norm hGn1).trans (hasSum_le hle2 hGn1.hasSum (hK.hasSum.mul_left t))
  generalize hKd : (∑' i, ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) = K at hmain
  have hK0 : 0 ≤ K := hKd ▸ tsum_nonneg fun i => by positivity
  by_contra hne
  have hc : 0 < ‖b 0‖ := norm_pos_iff.mpr hne
  have hK1 : (0 : ℝ) < 2 * (K + 1) := by linarith
  have ht : 0 < min (1 / 2 : ℝ) (‖b 0‖ / (2 * (K + 1))) := lt_min (by norm_num) (div_pos hc hK1)
  have h1 := hmain _ ht (min_le_left _ _)
  have h2 : min (1 / 2 : ℝ) (‖b 0‖ / (2 * (K + 1))) * K ≤ ‖b 0‖ / (2 * (K + 1)) * K :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hK0
  have h3 : ‖b 0‖ ≤ ‖b 0‖ / (2 * (K + 1)) * K := h1.trans h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hK1] at h3
  nlinarith [mul_nonneg hc.le hK0]
private theorem coeff_eq_zero_of_ev_eq_zero_of_lower_eq_zero {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) (n : ℕ)
    (ih : ∀ j < n, PowerSeries.coeff j f = 0) : PowerSeries.coeff n f = 0 := by
  have key := eq_zero_at_zero_of_tsum_mul_pow_eq_zero (fun i => PowerSeries.coeff (i + n) f) ?_ ?_
  · simpa using key
  · have h2 : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
      norm_num
    have hs := (summable_nat_add_iff n).mpr (hf _ h2)
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hs
    refine (hs.mul_left (2 ^ n)).congr fun i => ?_
    beta_reduce
    generalize ‖PowerSeries.coeff (i + n) f‖ = c
    rw [pow_add]
    calc (2 : ℝ) ^ n * (c * ((1 / 2) ^ i * (1 / 2) ^ n)) = c * (1 / 2) ^ i * ((1 / 2) ^ n * 2 ^ n) := by
          ring
      _ = c * (1 / 2) ^ i := by rw [← mul_pow]; norm_num
  · intro t ht hle
    have hx : ‖(t : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
      linarith
    have hx0 : 0 < ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact ht
    have hev := h _ hx0 hx
    have hsupp : Function.support (fun j => PowerSeries.coeff j f * (t : ℂ) ^ j) ⊆
        Set.range (fun i : ℕ => i + n) := by
      intro j hj
      by_cases hjn : j < n
      · rw [Function.mem_support] at hj
        exact absurd (by simp [ih j hjn]) hj
      · exact ⟨j - n, Nat.sub_add_cancel (not_lt.mp hjn)⟩
    have e1 : ev f (t : ℂ) = ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ (i + n) :=
      ((add_left_injective n).tsum_eq hsupp).symm
    have e2 : ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ (i + n) =
        (t : ℂ) ^ n * ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ i := by
      rw [← tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [e1, e2] at hev
    have htn : (t : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast ht.ne')
    exact (mul_eq_zero.mp hev).resolve_left htn
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) : f = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih => exact coeff_eq_zero_of_ev_eq_zero_of_lower_eq_zero hf h n ih
end ReciprocityTheory.ChartRestriction.L1
