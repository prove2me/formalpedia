-- Prove2me | solution 1 for Sendov.Jsum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:20.856931+00:00
-- url     : https://prove2.me/submissions/f89b04e2-5ecb-442b-b257-bdb6f7751273

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sum_map_sub
import Theorems.Thm_Sendov_sum_map_const_sub
import Theorems.Thm_Sendov_norm_sum_map_le
import Theorems.Thm_Sendov_norm_prod_le_one
import Theorems.Thm_Sendov_prod_mul_sum_inv
import Theorems.Thm_Sendov_sumEraseProd_norm_le_one
import Theorems.Thm_Sendov_defect
import Theorems.Thm_Sendov_norm_multiset_prod
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {z q : Multiset ℂ}
    (hqcard : q.card = n - 1)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod)‖
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hratio : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hn1]; linarith
  have hqpnorm : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  rcases eq_or_ne z.prod 0 with hz0 | hz0
  · -- degenerate: `J = 0`, and `sumEraseProd z` has at most one surviving term
    rw [hz0, mul_zero, mul_zero, sub_zero, norm_zero, mul_zero, norm_mul]
    have h2 : ‖sumEraseProd z‖ ≤ 1 := sumEraseProd_norm_le_one z hz1 hz0
    nlinarith [norm_nonneg q.prod, norm_nonneg (sumEraseProd z)]
  · -- the main case: every `zⱼ` is nonzero, so denominators may be cleared
    have hzne : ∀ w ∈ z, w ≠ 0 := by
      intro w hw hw0
      exact hz0 (Multiset.prod_eq_zero (hw0 ▸ hw))
    set qc : Multiset ℂ := q.map (fun v => (starRingEnd ℂ) v) with hqc
    have hqcnorm : ∀ w ∈ qc, ‖w‖ ≤ 1 := by
      intro w hw
      rw [hqc] at hw
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hw
      simpa using hq1 v hv
    have hqsum : q.sum = (qc.map (fun w => (starRingEnd ℂ) w)).sum := by
      rw [hqc, Multiset.map_map]
      simp
    -- the conjugated centroid identity
    have hconj : ((n : ℂ) - 1) * ((a : ℂ) + (z.map (fun w => (starRingEnd ℂ) w)).sum)
        = (n : ℂ) * (((n : ℂ) - 1) * (a : ℂ) - (qc.map (fun w => w⁻¹)).sum) := by
      have h := congrArg (starRingEnd ℂ) hcent
      simp only [map_mul, map_sub, map_add, map_one, map_inv₀, map_natCast,
        Complex.conj_ofReal, map_multiset_sum, Multiset.map_map, Function.comp_def] at h
      rw [sum_map_const_sub, hqcard] at h
      have hcard : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
        ring
      rw [hcard] at h
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def]
      exact h
    -- `J ∑ⱼ 1/zⱼ` in division-free form
    have hSz : q.prod * sumEraseProd z = (q.prod * z.prod) * (z.map (fun w => w⁻¹)).sum := by
      rw [← prod_mul_sum_inv z hzne]; ring
    -- name the error and the bracket
    obtain ⟨E, hEdef⟩ : ∃ w : ℂ, w = q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod) := ⟨_, rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ w : ℂ, w = ((n : ℂ) - 1)
          * ((z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum)
        + (n : ℂ) * (q.sum - (qc.map (fun w => w⁻¹)).sum) := ⟨_, rfl⟩
    rw [← hEdef]
    -- the exact rearrangement
    have hE : ((n : ℂ) - 1) * E = (q.prod * z.prod) * X := by
      rw [hEdef, hXdef, hSz, hxy]
      linear_combination (q.prod * z.prod) * hconj
    -- the defect lemma, applied to `z` together with the conjugates of `q`
    have hdefect := defect (z + qc) (by
      intro w hw
      rcases Multiset.mem_add.1 hw with h | h
      · exact hz1 w h
      · exact hqcnorm w h)
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.sum_add] at hdefect
    have hzp : (z.map (fun w => ‖w‖)).prod = ‖z.prod‖ := (norm_multiset_prod z).symm
    have hqp : (qc.map (fun w => ‖w‖)).prod = ‖q.prod‖ := by
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def, RCLike.norm_conj]
      exact (norm_multiset_prod q).symm
    rw [hzp, hqp] at hdefect
    obtain ⟨Dz, hDz⟩ : ∃ r : ℝ, r = (z.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ r : ℝ, r = (qc.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    rw [← hDz, ← hDq] at hdefect
    have hDz0 : 0 ≤ Dz := by
      rw [hDz]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    have hDq0 : 0 ≤ Dq := by
      rw [hDq]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    -- the two substitution errors
    have hbz : ‖(z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum‖ ≤ Dz := by
      rw [← sum_map_sub, hDz]
      exact norm_sum_map_le z _
    have hbq : ‖q.sum - (qc.map (fun w => w⁻¹)).sum‖ ≤ Dq := by
      have hneg : q.sum - (qc.map (fun w => w⁻¹)).sum
          = -((qc.map (fun w => w⁻¹ - (starRingEnd ℂ) w)).sum) := by
        rw [hqsum, sum_map_sub]
        ring
      rw [hneg, norm_neg, hDq]
      exact norm_sum_map_le qc _
    -- assemble
    have hnorm : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
      have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
    have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    have hXle : ‖X‖ ≤ ((n : ℝ) - 1) * Dz + (n : ℝ) * Dq := by
      rw [hXdef]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hnorm, hnn]
      exact add_le_add (mul_le_mul_of_nonneg_left hbz (by linarith))
        (mul_le_mul_of_nonneg_left hbq (by positivity))
    have hkey : ((n : ℝ) - 1) * ‖E‖ = ‖q.prod‖ * ‖z.prod‖ * ‖X‖ := by
      have h := congrArg norm hE
      rw [norm_mul, norm_mul, norm_mul, hnorm] at h
      exact h
    have hP0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
    have hstep : ((n : ℝ) - 1) * ‖E‖ ≤ (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
      rw [hkey]
      calc ‖q.prod‖ * ‖z.prod‖ * ‖X‖
          ≤ ‖q.prod‖ * ‖z.prod‖ * (((n : ℝ) - 1) * Dz + (n : ℝ) * Dq) :=
            mul_le_mul_of_nonneg_left hXle hP0
        _ ≤ ‖q.prod‖ * ‖z.prod‖ * ((n : ℝ) * (Dz + Dq)) := by nlinarith [hDz0, hP0]
        _ = (n : ℝ) * (‖z.prod‖ * ‖q.prod‖ * (Dz + Dq)) := by ring
        _ ≤ (n : ℝ) * (1 - (‖z.prod‖ * ‖q.prod‖) ^ 2) := by
            have hnpos : (0 : ℝ) ≤ (n : ℝ) := by linarith
            exact mul_le_mul_of_nonneg_left hdefect hnpos
        _ = (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hn1]
    linarith [hstep]
end Sendov
