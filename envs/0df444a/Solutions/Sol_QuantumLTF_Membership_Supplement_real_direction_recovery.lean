-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.real_direction_recovery
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:35:02.39831+00:00
-- url     : https://prove2.me/submissions/979a900d-4f4b-4f3b-8125-528682a02638

import Mathlib

set_option autoImplicit false

theorem section5_normalize_perturbation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x-y‖ / ‖y‖ := by
  have hnx : ‖NormedSpace.normalize x‖ = 1 := NormedSpace.norm_normalize hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have heq : ‖y‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (‖y‖-‖x‖) • NormedSpace.normalize x + (x-y) := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  have hh := norm_add_le ((‖y‖-‖x‖) • NormedSpace.normalize x) (x-y)
  rw [← heq, norm_smul, Real.norm_of_nonneg (norm_nonneg y), norm_smul,
    Real.norm_eq_abs, hnx, mul_one] at hh
  have hl : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
    simpa [abs_sub_comm] using abs_norm_sub_norm_le x y
  apply (le_div_iff₀ hny).mpr
  nlinarith

theorem section5_normalize_real_direction {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (r w : V) (c δ : ℝ) (hw : ‖w‖ = 1)
    (hc : 1/2 < |c|) (hδ : 0 ≤ δ) (hδ' : δ < 1/2)
    (hclose : ‖r - c • w‖ ≤ δ) :
    r ≠ 0 ∧ ‖‖r‖⁻¹ • r - (SignType.sign c : ℝ) • w‖ ≤ 4 * δ := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hc0 : c ≠ 0 := abs_pos.mp (by linarith)
  have hcw : ‖c • w‖ = |c| := by simp [norm_smul, hw]
  have hr : r ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, hcw] at hclose
    linarith
  refine ⟨hr, ?_⟩
  have hn := section5_normalize_perturbation r (c • w) hr (smul_ne_zero hc0 hw0)
  rw [NormedSpace.normalize_smul,
    NormedSpace.normalize_eq_self_of_norm_eq_one hw, hcw] at hn
  change ‖‖r‖⁻¹ • r - (SignType.sign c : ℝ) • w‖ ≤ _ at hn
  have hb : 2 * ‖r-c • w‖ / |c| ≤ 4 * δ := by
    apply (div_le_iff₀ (lt_trans (by norm_num) hc)).mpr
    nlinarith
  exact hn.trans hb

set_option autoImplicit false

noncomputable def section5_real_part {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (v i).re

noncomputable def section5_imag_part {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (v i).im

noncomputable def section5_complexify {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun i => (w i : ℂ)

theorem section5_parts_norm_sq {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖^2 + ‖section5_imag_part v‖^2 = ‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, section5_real_part, section5_imag_part,
    WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem section5_real_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_real_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).re‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  nlinarith [norm_nonneg (section5_real_part v), norm_nonneg v]

theorem section5_imag_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_imag_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_imag_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).im‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  nlinarith [norm_nonneg (section5_imag_part v), norm_nonneg v]

theorem solution {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (ζ : ℂ) (ε : ℝ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hε : 0 < ε) (hε' : ε < 1)
    (hclose : ‖v - ζ • section5_complexify w‖ ≤ ε/24) :
    let a := section5_real_part v
    let b := section5_imag_part v
    let r := if ‖b‖ ≤ ‖a‖ then a else b
    r ≠ 0 ∧
      (‖‖r‖⁻¹ • r - w‖ ≤ ε/6 ∨ ‖‖r‖⁻¹ • r + w‖ ≤ ε/6) := by
  classical
  let a := section5_real_part v
  let b := section5_imag_part v
  let r := if ‖b‖ ≤ ‖a‖ then a else b
  let c : ℝ := if ‖b‖ ≤ ‖a‖ then ζ.re else ζ.im
  have hparts : ‖a‖^2 + ‖b‖^2 = 1 := by
    simpa [a, b, hv] using section5_parts_norm_sq v
  have hbig : 2/3 < ‖r‖ := by
    dsimp [r]
    split_ifs with h
    · nlinarith [norm_nonneg a, norm_nonneg b]
    · push Not at h
      nlinarith [norm_nonneg a, norm_nonneg b]
  have hrc : ‖r - c • w‖ ≤ ε/24 := by
    have hre : section5_real_part (v - ζ • section5_complexify w) = a - ζ.re • w := by
      ext i
      simp [section5_real_part, section5_complexify, a, Complex.mul_re]
    have him : section5_imag_part (v - ζ • section5_complexify w) = b - ζ.im • w := by
      ext i
      simp [section5_imag_part, section5_complexify, b, Complex.mul_im]
    dsimp [r, c]
    split_ifs
    · rw [← hre]
      exact (section5_real_part_contraction _).trans hclose
    · rw [← him]
      exact (section5_imag_part_contraction _).trans hclose
  have hc : 1/2 < |c| := by
    have hh := norm_sub_norm_le r (c • w)
    rw [norm_smul, hw, Real.norm_eq_abs, mul_one] at hh
    linarith
  obtain ⟨hr, hresult⟩ := section5_normalize_real_direction r w c (ε/24) hw hc
    (by positivity) (by linarith) hrc
  change r ≠ 0 ∧ _
  refine ⟨hr, ?_⟩
  change ‖‖r‖⁻¹ • r - w‖ ≤ ε/6 ∨ ‖‖r‖⁻¹ • r + w‖ ≤ ε/6
  have hconst : 4*(ε/24) = ε/6 := by ring
  rw [hconst] at hresult
  rcases lt_or_gt_of_ne (abs_pos.mp (show 0 < |c| by linarith)) with hneg | hpos
  · right
    simpa [sign_neg hneg, sub_eq_add_neg] using hresult
  · left
    simpa [sign_pos hpos] using hresult
