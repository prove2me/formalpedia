-- Prove2me | solution 1 for RiskBalancingMNL.eq_13_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:40:21.287194+00:00
-- url     : https://prove2.me/submissions/7e02d2a9-9ee7-4b25-aaed-ed406e7c3104

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat
import Theorems.Thm_RiskBalancingMNL_markup_share_inverse

open RiskBalancingMNL

private lemma hasDerivAt_mHat {n : ℕ} (P : Params n) {y : ℝ} (hy : y ∈ Set.Ioo 0 1) :
    HasDerivAt (mHat P) (1 / (P.b * y * (1 - y))) y := by
  have hy_pos : 0 < y := hy.1
  have h1y_pos : 0 < 1 - y := sub_pos.mpr hy.2
  have hz : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
  have h1z : HasDerivAt (fun z : ℝ => 1 - z) (0 - 1) y :=
    (hasDerivAt_const y 1).fun_sub hz
  have hquot : HasDerivAt (fun z : ℝ => z / (1 - z)) (1 / (1 - y) ^ 2) y :=
    (hz.fun_div h1z h1y_pos.ne').congr_deriv (by ring)
  have hlog : HasDerivAt (fun z : ℝ => Real.log (z / (1 - z)))
      ((1 / (1 - y) ^ 2) / (y / (1 - y))) y :=
    hquot.log (div_pos hy_pos h1y_pos).ne'
  have hnum := (hasDerivAt_const y (Real.log (zeroMarkupMass P))).fun_add hlog
  have hdiv := hnum.fun_div (hasDerivAt_const y P.b) P.hb.ne'
  refine hdiv.congr_deriv ?_
  have hb_ne : P.b ≠ 0 := P.hb.ne'
  have hy_ne : y ≠ 0 := hy_pos.ne'
  have h1y_ne : 1 - y ≠ 0 := h1y_pos.ne'
  field_simp [hb_ne, hy_ne, h1y_ne]
  ring

theorem solution {n : ℕ} [NeZero n] (P : Params n) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam : lam < lamBar P) :
    StrictMonoOn (foc P lam) (Set.Ioo 0 (1 - lam)) ∧
    (∃! x : ℝ, x ∈ Set.Ioo 0 (1 - lam) ∧ foc P lam x = 0) ∧
    ∀ x ∈ Set.Ioo 0 (1 - lam), foc P lam x = 0 → 1 - lamBar P < x := by
  obtain ⟨_, _, hmHat_left, hmHat_mono⟩ := markup_share_inverse P
  have hA_pos : 0 < zeroMarkupMass P :=
    (Real.exp_pos _).trans_le
      (Finset.single_le_sum (f := fun i => Real.exp (P.a i - P.b * P.c i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Fin n)))
  have hlamBar_pos : 0 < lamBar P := div_pos hA_pos (by linarith)
  have hlamBar_lt1 : lamBar P < 1 := by
    unfold lamBar
    rw [div_lt_one (by linarith)]
    linarith
  let x0 : ℝ := 1 - lamBar P
  have hx0_pos : 0 < x0 := by dsimp [x0]; linarith
  have hx0_lt_1lam : x0 < 1 - lam := by dsimp [x0]; linarith
  have hx0_mem : x0 ∈ Set.Ioo 0 (1 - lam) := ⟨hx0_pos, hx0_lt_1lam⟩
  have hq0_zero : noPurchase P (constM 0) = x0 := by
    have hattr0 : ∑ j, attraction P (constM 0) j = zeroMarkupMass P := by
      unfold attraction constM zeroMarkupMass
      refine Finset.sum_congr rfl fun j _ => ?_
      ring_nf
    unfold noPurchase x0 lamBar
    rw [hattr0]
    have hden : 1 + zeroMarkupMass P ≠ 0 := by linarith
    field_simp [hden]
    ring
  have hmHat_x0 : mHat P x0 = 0 := by
    rw [← hq0_zero]
    exact hmHat_left 0
  have hfoc_deriv : ∀ y ∈ Set.Ioo 0 (1 - lam),
      HasDerivAt (foc P lam)
        (1 / (P.b * y * (1 - y)) + 1 / (P.b * y ^ 2) +
          lam * (1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) -
            mHat P y * (-2)) / (2 * (1 - y - lam)) ^ 2) y := by
    intro y hy
    have hy_pos : 0 < y := hy.1
    have hy_lt1 : y < 1 := by linarith [hy.2]
    have hu_pos : 0 < 1 - y - lam := by linarith [hy.2]
    have hm := hasDerivAt_mHat P ⟨hy_pos, hy_lt1⟩
    have hby : HasDerivAt (fun z : ℝ => P.b * z) (P.b * 1) y :=
      (hasDerivAt_id y).const_mul P.b
    have hterm2 : HasDerivAt (fun z : ℝ => 1 / (P.b * z)) (-1 / (P.b * y ^ 2)) y := by
      have hd := (hasDerivAt_const y (1 : ℝ)).fun_div hby (mul_pos P.hb hy_pos).ne'
      refine hd.congr_deriv ?_
      have hb_ne : P.b ≠ 0 := P.hb.ne'
      have hy_ne : y ≠ 0 := hy_pos.ne'
      field_simp [hb_ne, hy_ne]
      ring
    have hden3 : HasDerivAt (fun z : ℝ => 2 * (1 - z - lam)) (-2) y := by
      have h1 : HasDerivAt (fun z : ℝ => 1 - z - lam) (0 - 1 - 0) y :=
        ((hasDerivAt_const y 1).fun_sub (hasDerivAt_id y)).fun_sub (hasDerivAt_const y lam)
      have h2 := h1.const_mul 2
      exact h2.congr_deriv (by ring)
    have hnum3 : HasDerivAt (fun z : ℝ => lam * mHat P z)
        (lam * (1 / (P.b * y * (1 - y)))) y := hm.const_mul lam
    have hterm3 := hnum3.fun_div hden3 (by linarith : 2 * (1 - y - lam) ≠ 0)
    have hall := (hm.fun_sub hterm2).fun_add hterm3
    refine hall.congr_deriv ?_
    have hu_ne : 2 * (1 - y - lam) ≠ 0 := by linarith
    ring
  have hfoc_deriv_pos : ∀ y ∈ Set.Ioo 0 (1 - lam), 0 < deriv (foc P lam) y := by
    intro y hy
    rw [(hfoc_deriv y hy).deriv]
    have hy_pos : 0 < y := hy.1
    have hy_lt1 : y < 1 := by linarith [hy.2]
    have h1y_pos : 0 < 1 - y := sub_pos.mpr hy_lt1
    have hu_pos : 0 < 1 - y - lam := by linarith [hy.2]
    have hb_pos : 0 < P.b := P.hb
    by_cases hyx0 : x0 ≤ y
    · have hm_nonneg : 0 ≤ mHat P y := by
        rcases eq_or_lt_of_le hyx0 with rfl | hlt
        · exact hmHat_x0.ge
        · rw [← hmHat_x0]
          exact (hmHat_mono ⟨hx0_pos, by linarith⟩ ⟨hy_pos, hy_lt1⟩ hlt).le
      have ht1 : 0 < 1 / (P.b * y * (1 - y)) :=
        div_pos zero_lt_one (mul_pos (mul_pos hb_pos hy_pos) h1y_pos)
      have ht2 : 0 < 1 / (P.b * y ^ 2) :=
        div_pos zero_lt_one (mul_pos hb_pos (sq_pos_of_pos hy_pos))
      have ht3_num : 0 ≤ lam * (1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) -
          mHat P y * (-2)) := by
        refine mul_nonneg hlam0 ?_
        have hp1 : 0 ≤ 1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) :=
          mul_nonneg ht1.le (by linarith)
        nlinarith
      have ht3 : 0 ≤ lam * (1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) -
          mHat P y * (-2)) / (2 * (1 - y - lam)) ^ 2 :=
        div_nonneg ht3_num (sq_nonneg _)
      linarith
    · have hy_lt_x0 : y < x0 := lt_of_not_ge hyx0
      let d : ℝ := x0 - y
      let δ : ℝ := lamBar P - lam
      have hd_pos : 0 < d := sub_pos.mpr hy_lt_x0
      have hδ_pos : 0 < δ := sub_pos.mpr hlam
      have hbm_lb : -(d / (lamBar P * y)) ≤ P.b * mHat P y := by
        have hbm_eq : P.b * mHat P y = Real.log (zeroMarkupMass P * (y / (1 - y))) := by
          unfold mHat
          rw [mul_div_cancel₀ _ hb_pos.ne',
            Real.log_mul hA_pos.ne' (div_pos hy_pos h1y_pos).ne']
        rw [hbm_eq]
        let z : ℝ := zeroMarkupMass P * (y / (1 - y))
        have hz_pos : 0 < z := mul_pos hA_pos (div_pos hy_pos h1y_pos)
        have hinv_le := Real.log_le_sub_one_of_pos (inv_pos.mpr hz_pos)
        rw [Real.log_inv] at hinv_le
        have hlog_ge : 1 - z⁻¹ ≤ Real.log z := by linarith
        have hz_ratio : 1 - z⁻¹ = -(d / (lamBar P * y)) := by
          dsimp [z, d, x0, lamBar]
          have h1A : 1 + zeroMarkupMass P ≠ 0 := by linarith
          have hA_ne : zeroMarkupMass P ≠ 0 := hA_pos.ne'
          have hy_ne : y ≠ 0 := hy_pos.ne'
          have h1y_ne : 1 - y ≠ 0 := h1y_pos.ne'
          field_simp [h1A, hA_ne, hy_ne, h1y_ne]
          ring
        rwa [hz_ratio] at hlog_ge
      let Dbig : ℝ := P.b * y ^ 2 * (1 - y) * (2 * (1 - y - lam)) ^ 2 * lamBar P
      have hDbig_pos : 0 < Dbig := by
        dsimp [Dbig]
        positivity
      have hprod_pos : 0 < Dbig *
          (1 / (P.b * y * (1 - y)) + 1 / (P.b * y ^ 2) +
            lam * (1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) -
              mHat P y * (-2)) / (2 * (1 - y - lam)) ^ 2) := by
        have hrew : Dbig *
            (1 / (P.b * y * (1 - y)) + 1 / (P.b * y ^ 2) +
              lam * (1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) -
                mHat P y * (-2)) / (2 * (1 - y - lam)) ^ 2) =
            y * (2 * (1 - y - lam)) ^ 2 * lamBar P +
              (1 - y) * (2 * (1 - y - lam)) ^ 2 * lamBar P +
              2 * y * lam * (1 - y - lam) * lamBar P +
              2 * y ^ 2 * (1 - y) * lam * lamBar P * (P.b * mHat P y) := by
          dsimp [Dbig]
          have hb_ne : P.b ≠ 0 := hb_pos.ne'
          have hy_ne : y ≠ 0 := hy_pos.ne'
          have h1y_ne : 1 - y ≠ 0 := h1y_pos.ne'
          have hu_ne : 2 * (1 - y - lam) ≠ 0 := by linarith
          field_simp [hb_ne, hy_ne, h1y_ne, hu_ne]
          ring
        rw [hrew]
        have hcoef_nonneg : 0 ≤ 2 * y ^ 2 * (1 - y) * lam * lamBar P := by positivity
        have hstep1 : 2 * y ^ 2 * (1 - y) * lam * lamBar P * (-(d / (lamBar P * y))) ≤
            2 * y ^ 2 * (1 - y) * lam * lamBar P * (P.b * mHat P y) :=
          mul_le_mul_of_nonneg_left hbm_lb hcoef_nonneg
        have hsimp_neg : 2 * y ^ 2 * (1 - y) * lam * lamBar P * (-(d / (lamBar P * y))) =
            -(2 * y * (1 - y) * lam * d) := by
          have hlB_ne : lamBar P ≠ 0 := hlamBar_pos.ne'
          have hy_ne : y ≠ 0 := hy_pos.ne'
          field_simp [hlB_ne, hy_ne]
        rw [hsimp_neg] at hstep1
        have hpoly : y * (2 * (1 - y - lam)) ^ 2 * lamBar P +
              (1 - y) * (2 * (1 - y - lam)) ^ 2 * lamBar P +
              2 * y * lam * (1 - y - lam) * lamBar P -
              2 * y * (1 - y) * lam * d =
            4 * (d + lam + δ) * (d + δ) ^ 2 * (lam + δ) +
              2 * y * (d ^ 2 * lam + 2 * d ^ 2 * δ + 4 * d * δ * lam +
                4 * d * δ ^ 2 + 3 * δ ^ 2 * lam + 2 * δ ^ 3 + δ * lam ^ 2) := by
          have h1y_eq : 1 - y = d + lam + δ := by dsimp [d, δ, x0]; ring
          have hlB_eq : lamBar P = lam + δ := by dsimp [δ]; ring
          rw [h1y_eq, hlB_eq]
          ring
        have hpoly_pos : 0 < 4 * (d + lam + δ) * (d + δ) ^ 2 * (lam + δ) +
            2 * y * (d ^ 2 * lam + 2 * d ^ 2 * δ + 4 * d * δ * lam +
              4 * d * δ ^ 2 + 3 * δ ^ 2 * lam + 2 * δ ^ 3 + δ * lam ^ 2) := by
          positivity
        linarith
      by_contra hle
      have : Dbig *
          (1 / (P.b * y * (1 - y)) + 1 / (P.b * y ^ 2) +
            lam * (1 / (P.b * y * (1 - y)) * (2 * (1 - y - lam)) -
              mHat P y * (-2)) / (2 * (1 - y - lam)) ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hDbig_pos.le (not_lt.mp hle)
      linarith
  have hfoc_cont : ContinuousOn (foc P lam) (Set.Ioo 0 (1 - lam)) :=
    fun y hy => (hfoc_deriv y hy).continuousAt.continuousWithinAt
  have hfoc_mono : StrictMonoOn (foc P lam) (Set.Ioo 0 (1 - lam)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo 0 (1 - lam)) hfoc_cont ?_
    rw [isOpen_Ioo.interior_eq]
    exact hfoc_deriv_pos
  have hfoc_x0 : foc P lam x0 < 0 := by
    unfold foc
    rw [hmHat_x0]
    simp only [mul_zero, zero_div, add_zero, zero_sub, Right.neg_neg_iff]
    exact div_pos zero_lt_one (mul_pos P.hb hx0_pos)
  have hgt_x0 : ∀ x ∈ Set.Ioo 0 (1 - lam), foc P lam x = 0 → x0 < x := by
    intro x hx hroot
    by_contra hle
    rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | rfl
    · have := hfoc_mono hx hx0_mem hlt
      linarith
    · linarith
  have hex_upper : ∃ x1 ∈ Set.Ioo x0 (1 - lam), 0 ≤ foc P lam x1 := by
    rcases eq_or_lt_of_le hlam0 with rfl | hlam_pos
    · let x1 : ℝ := max ((x0 + 1) / 2)
        (max (1 / 2) (Real.exp 2 / (zeroMarkupMass P + Real.exp 2)))
      have hx0_lt1 : x0 < 1 := by linarith
      have hexp2_pos : 0 < Real.exp 2 := Real.exp_pos 2
      have hx1_gt_x0 : x0 < x1 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hx1_lt1 : x1 < 1 - 0 := by
        simp only [sub_zero]
        refine max_lt (by linarith) (max_lt (by norm_num) ?_)
        rw [div_lt_one (by linarith)]
        linarith
      have hx1_ge_half : (1 / 2 : ℝ) ≤ x1 :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hx1_ge_exp : Real.exp 2 / (zeroMarkupMass P + Real.exp 2) ≤ x1 :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hx1_pos : 0 < x1 := by linarith
      have h1x1_pos : 0 < 1 - x1 := by linarith
      refine ⟨x1, ⟨hx1_gt_x0, hx1_lt1⟩, ?_⟩
      have hexp_le : Real.exp 2 ≤ zeroMarkupMass P * (x1 / (1 - x1)) := by
        rw [div_le_iff₀ (by linarith)] at hx1_ge_exp
        rw [← mul_div_assoc, le_div_iff₀ h1x1_pos]
        linarith
      have hlog_ge : 2 ≤ Real.log (zeroMarkupMass P) + Real.log (x1 / (1 - x1)) := by
        rw [← Real.log_mul hA_pos.ne' (div_pos hx1_pos h1x1_pos).ne']
        have := Real.log_le_log hexp2_pos hexp_le
        rwa [Real.log_exp] at this
      have hinv_le : 1 / x1 ≤ 2 := by
        rw [div_le_iff₀ hx1_pos]
        linarith
      unfold foc mHat
      simp only [zero_mul, zero_div, add_zero]
      have hrew : (Real.log (zeroMarkupMass P) + Real.log (x1 / (1 - x1))) / P.b -
          1 / (P.b * x1) =
          (Real.log (zeroMarkupMass P) + Real.log (x1 / (1 - x1)) - 1 / x1) / P.b := by
        have hb_ne : P.b ≠ 0 := P.hb.ne'
        have hx1_ne : x1 ≠ 0 := hx1_pos.ne'
        field_simp [hb_ne, hx1_ne]
      rw [hrew]
      exact div_nonneg (by linarith) P.hb.le
    · let xm : ℝ := (x0 + (1 - lam)) / 2
      have hxm_gt : x0 < xm := by dsimp [xm]; linarith
      have hxm_lt : xm < 1 - lam := by dsimp [xm]; linarith
      have hxm_pos : 0 < xm := hx0_pos.trans hxm_gt
      have hmm_pos : 0 < mHat P xm := by
        rw [← hmHat_x0]
        exact hmHat_mono ⟨hx0_pos, by linarith⟩ ⟨hxm_pos, by linarith⟩ hxm_gt
      let ε : ℝ := min ((1 - lam - xm) / 2) (lam * mHat P xm * P.b * xm / 2)
      have hε_pos : 0 < ε :=
        lt_min (by linarith)
          (div_pos (mul_pos (mul_pos (mul_pos hlam_pos hmm_pos) P.hb) hxm_pos) zero_lt_two)
      have hε_le1 : ε ≤ (1 - lam - xm) / 2 := min_le_left _ _
      have hε_le2 : ε ≤ lam * mHat P xm * P.b * xm / 2 := min_le_right _ _
      let x1 : ℝ := 1 - lam - ε
      have hx1_gt_xm : xm < x1 := by dsimp [x1]; linarith
      have hx1_lt : x1 < 1 - lam := by dsimp [x1]; linarith
      have hx1_pos : 0 < x1 := hxm_pos.trans hx1_gt_xm
      refine ⟨x1, ⟨hxm_gt.trans hx1_gt_xm, hx1_lt⟩, ?_⟩
      have hm1_ge : mHat P xm ≤ mHat P x1 :=
        (hmHat_mono ⟨hxm_pos, by linarith⟩ ⟨hx1_pos, by linarith⟩ hx1_gt_xm).le
      have hbx_le : 1 / (P.b * x1) ≤ 1 / (P.b * xm) :=
        one_div_le_one_div_of_le (mul_pos P.hb hxm_pos)
          (mul_le_mul_of_nonneg_left hx1_gt_xm.le P.hb.le)
      have h1x1_eq : 1 - x1 - lam = ε := by dsimp [x1]; ring
      have h3_ge : 1 / (P.b * xm) ≤ lam * mHat P x1 / (2 * (1 - x1 - lam)) := by
        rw [h1x1_eq, div_le_div_iff₀ (mul_pos P.hb hxm_pos) (by linarith)]
        have hmul1 : lam * mHat P xm ≤ lam * mHat P x1 :=
          mul_le_mul_of_nonneg_left hm1_ge hlam_pos.le
        have hmul2 : lam * mHat P xm * (P.b * xm) ≤ lam * mHat P x1 * (P.b * xm) :=
          mul_le_mul_of_nonneg_right hmul1 (mul_pos P.hb hxm_pos).le
        linarith
      unfold foc
      linarith
  obtain ⟨x1, hx1_mem, hfoc_x1⟩ := hex_upper
  have hx0_le_x1 : x0 ≤ x1 := hx1_mem.1.le
  have hIcc_sub : Set.Icc x0 x1 ⊆ Set.Ioo 0 (1 - lam) :=
    fun z hz => ⟨hx0_pos.trans_le hz.1, hz.2.trans_lt hx1_mem.2⟩
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (foc P lam x0) (foc P lam x1) := ⟨hfoc_x0.le, hfoc_x1⟩
  obtain ⟨x_root, hx_in, hx_eq⟩ :=
    intermediate_value_Icc hx0_le_x1 (hfoc_cont.mono hIcc_sub) hzero_mem
  refine ⟨hfoc_mono, ⟨x_root, ⟨hIcc_sub hx_in, hx_eq⟩, ?_⟩, hgt_x0⟩
  rintro y ⟨hy_mem, hy_eq⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hfoc_mono hy_mem (hIcc_sub hx_in) hlt
    linarith
  · have := hfoc_mono (hIcc_sub hx_in) hy_mem hgt
    linarith
