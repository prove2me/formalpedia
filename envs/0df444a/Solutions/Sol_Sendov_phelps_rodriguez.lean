-- Prove2me | solution 1 for Sendov.phelps_rodriguez
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:36:57.740005+00:00
-- url     : https://prove2.me/submissions/0e15a180-beaf-4feb-b662-4be578fff4f4

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
import Theorems.Thm_Sendov_eval_rotate
import Theorems.Thm_Sendov_natDegree_rotate
import Theorems.Thm_Sendov_eval_derivative_rotate
import Theorems.Thm_Sendov_rotate_rotate_inv
import Theorems.Thm_Sendov_roots_rotate
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_rubinstein_one
import Theorems.Thm_Sendov_sendov_center
import Theorems.Thm_Sendov_sendov_interior_real
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_wsum_nil
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero
attribute [local simp] Sendov.wsumZ_cons
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.wsum_nil


attribute [local simp] Sendov.eval_rotate

set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧ p = C c * (X ^ n - C (a ^ n))) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn hdeg hroots hpa
    exact Or.inl ⟨ζ, hζ, by simpa using hlt⟩
  -- the rotation `a = ω r`
  have hr0 : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hr1 : ‖a‖ ≤ 1 := hroots a (mem_roots'.2 ⟨hp0, hpa⟩)
  have hrC : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hr0
  obtain ⟨ω, hωdef⟩ : ∃ w : ℂ, w = a / ((‖a‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hωne : ω ≠ 0 := by
    rw [hωdef]
    exact div_ne_zero ha0 hrC
  have hωnorm : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr0),
      div_self (ne_of_gt hr0)]
  have hωr : ω * ((‖a‖ : ℝ) : ℂ) = a := by
    rw [hωdef, div_mul_cancel₀ _ hrC]
  -- the rotated polynomial
  have hdeg' : (rotate ω p).natDegree = n := by rw [natDegree_rotate hωne, hdeg]
  have hroots' := roots_rotate hωnorm hp0 hroots
  have hpr : (rotate ω p).eval ((‖a‖ : ℝ) : ℂ) = 0 := by rw [eval_rotate, hωr, hpa]
  -- transporting a strict witness back
  have htransport : ∀ ζ : ℂ, (derivative (rotate ω p)).eval ζ = 0 →
      ‖ζ - ((‖a‖ : ℝ) : ℂ)‖ < 1 → ∃ ξ : ℂ, (derivative p).eval ξ = 0 ∧ ‖ξ - a‖ < 1 := by
    intro ζ hζ hlt
    refine ⟨ω * ζ, ?_, ?_⟩
    · rw [eval_derivative_rotate] at hζ
      exact (mul_eq_zero.1 hζ).resolve_left hωne
    · have : ω * ζ - a = ω * (ζ - ((‖a‖ : ℝ) : ℂ)) := by rw [mul_sub, hωr]
      rw [this, norm_mul, hωnorm, one_mul]
      exact hlt
  rcases lt_or_eq_of_le hr1 with hlt1 | heq1
  · -- the interior case
    obtain ⟨ζ, hζ, hd⟩ :=
      sendov_interior_real hn hdeg' hroots' (le_of_lt hr0) hlt1 hpr
    exact Or.inl (htransport ζ hζ hd)
  · -- the boundary case: `a = ω`
    have hone : ((‖a‖ : ℝ) : ℂ) = 1 := by rw [heq1]; norm_num
    have haω : a = ω := by rw [← hωr, hone, mul_one]
    have hpr1 : (rotate ω p).eval 1 = 0 := by rwa [hone] at hpr
    rcases rubinstein_one hn hdeg' hroots' hpr1 with ⟨ζ, hζ, hd⟩ | hext
    · exact Or.inl (htransport ζ hζ (by rw [hone]; exact hd))
    -- the extremal case, rotated back
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (rotate ω p).leadingCoeff := ⟨_, rfl⟩
    have hcne : c ≠ 0 := by
      rw [hcdef]
      refine leadingCoeff_ne_zero.2 ?_
      intro h
      rw [h, natDegree_zero] at hdeg'
      omega
    refine Or.inr ⟨heq1, c * ω⁻¹ ^ n,
      mul_ne_zero hcne (pow_ne_zero _ (inv_ne_zero hωne)), ?_⟩
    have hext' : rotate ω p = C c * (X ^ n - 1) := by rw [hcdef]; exact hext
    have hcomp : rotate ω⁻¹ (C c * (X ^ n - 1)) = C c * (C (ω⁻¹ ^ n) * X ^ n - 1) := by
      simp only [rotate, mul_comp, sub_comp, pow_comp, C_comp, X_comp, one_comp, mul_pow,
        ← C_pow]
    have h1 : (C (ω⁻¹ ^ n) * C (ω ^ n) : ℂ[X]) = 1 := by
      rw [← C_mul, ← mul_pow, inv_mul_cancel₀ hωne, one_pow, C_1]
    have hgoal : rotate ω⁻¹ (rotate ω p) = C (c * ω⁻¹ ^ n) * (X ^ n - C (a ^ n)) := by
      rw [hext', hcomp, haω, C_mul]
      linear_combination (C c) * h1
    exact (rotate_rotate_inv hωne p).symm.trans hgoal
end Sendov
