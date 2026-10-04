-- Prove2me | solution 1 for SennottDP.Tauberian.geometric_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:20:15.583653+00:00
-- url     : https://prove2.me/submissions/6970c2c5-a243-4df1-a47d-9016751edc08

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

set_option autoImplicit false

lemma p8e1d1a5a_tendsto (B : ℝ≥0) (hB : 0 < B) :
    Tendsto (fun n : ℕ => (B : ℝ≥0∞) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n : ℕ => (B : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hc := Real.continuousAt_const_rpow (a := (B : ℝ)) (b := 0)
      (by exact_mod_cast hB.ne')
    have h1 := hc.tendsto
    rw [Real.rpow_zero] at h1
    exact h1.comp h0
  have hN : Tendsto (fun n : ℕ => B ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    rw [← NNReal.tendsto_coe]
    simpa [NNReal.coe_rpow] using hR
  have hE := (ENNReal.tendsto_coe.mpr hN)
  refine hE.congr' (Eventually.of_forall fun n => ?_)
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)]

lemma p8e1d1a5a_nsum (α : ℝ≥0) (hα : α < 1) :
    ∑' n : ℕ, (n : ℝ≥0∞) * (α : ℝ≥0∞) ^ n = (α : ℝ≥0∞) / (1 - (α : ℝ≥0∞)) ^ 2 := by
  have hr : ‖(α : ℝ)‖ < 1 := by
    have h1 : (α : ℝ) < 1 := by exact_mod_cast hα
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [NNReal.coe_nonneg α]
  have hS := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hf : Summable (fun n : ℕ => (n : ℝ≥0) * α ^ n) := by
    rw [← NNReal.summable_coe]; simpa using hS.summable
  have hval : ∑' n : ℕ, (n : ℝ≥0) * α ^ n = α / (1 - α) ^ 2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_tsum]
    push_cast [NNReal.coe_sub hα.le]
    simpa using hS.tsum_eq
  have hne : (1 - α) ^ 2 ≠ 0 := pow_ne_zero _ (tsub_pos_of_lt hα).ne'
  calc ∑' n : ℕ, (n : ℝ≥0∞) * (α : ℝ≥0∞) ^ n
      = ∑' n : ℕ, (((n : ℝ≥0) * α ^ n : ℝ≥0) : ℝ≥0∞) := by
        push_cast; rfl
    _ = ((∑' n : ℕ, (n : ℝ≥0) * α ^ n : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_tsum hf).symm
    _ = (α : ℝ≥0∞) / (1 - (α : ℝ≥0∞)) ^ 2 := by
        rw [hval, ENNReal.coe_div hne, ENNReal.coe_pow, ENNReal.coe_sub, ENNReal.coe_one]

open SennottDP.Tauberian in open scoped ENNReal NNReal in
theorem solution (B : ℝ≥0) (hB : 0 < B) :
    radius (fun _ => (B : ℝ≥0∞)) = 1 ∧
      ∀ α : ℝ≥0, α < 1 →
        U (fun _ => (B : ℝ≥0∞)) α = (B : ℝ≥0∞) / (1 - (α : ℝ≥0∞)) ∧
          ∑' n : ℕ, (B : ℝ≥0∞) * (n : ℝ≥0∞) * (α : ℝ≥0∞) ^ n
            = (B : ℝ≥0∞) * (α : ℝ≥0∞) / (1 - (α : ℝ≥0∞)) ^ 2 := by
  refine ⟨?_, fun α hα => ⟨?_, ?_⟩⟩
  · unfold radius
    rw [(p8e1d1a5a_tendsto B hB).limsup_eq, inv_one]
  · unfold U
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, div_eq_mul_inv, mul_comm]
  · simp_rw [mul_assoc]
    rw [ENNReal.tsum_mul_left, p8e1d1a5a_nsum α hα, mul_div_assoc]

#print axioms solution
