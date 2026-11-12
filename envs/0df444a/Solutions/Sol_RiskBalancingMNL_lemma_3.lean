-- Prove2me | solution 1 for RiskBalancingMNL.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:48:43.037901+00:00
-- url     : https://prove2.me/submissions/845dc946-55a4-43b5-8940-e145c666c501

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat
import Theorems.Thm_RiskBalancingMNL_markup_share_inverse
import Theorems.Thm_RiskBalancingMNL_eq_13_unique_root

open RiskBalancingMNL

private lemma hasDerivAt_mHat_3 {n : ℕ} (P : Params n) {y : ℝ} (hy : y ∈ Set.Ioo 0 1) :
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
    (hlam : lam < lamBar P) (x : ℝ) (hx : x ∈ Set.Ioo 0 (1 - lam)) (hfoc : foc P lam x = 0) :
    StrictMonoOn (LTilde P lam) (Set.Icc (1 - lamBar P) x) ∧
    StrictAntiOn (LTilde P lam) (Set.Ico x (1 - lam)) := by
  obtain ⟨_, _, hmHat_left, hmHat_mono⟩ := markup_share_inverse P
  obtain ⟨hfoc_mono, _, hgt_x0⟩ := eq_13_unique_root P lam hlam0 hlam
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
  have hx0_lt_x : x0 < x := hgt_x0 x hx hfoc
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
  have hLTilde_deriv : ∀ y ∈ Set.Ioo 0 (1 - lam),
      HasDerivAt (LTilde P lam) (-2 * mHat P y * (1 - y - lam) * foc P lam y) y := by
    intro y hy
    have hy_pos : 0 < y := hy.1
    have hy_lt1 : y < 1 := by linarith [hy.2]
    have h1y_pos : 0 < 1 - y := sub_pos.mpr hy_lt1
    have hu_pos : 0 < 1 - y - lam := by linarith [hy.2]
    have hm := hasDerivAt_mHat_3 P ⟨hy_pos, hy_lt1⟩
    have hm2 := hm.fun_pow 2
    have h1z : HasDerivAt (fun z : ℝ => 1 - z) (0 - 1) y :=
      (hasDerivAt_const y 1).fun_sub (hasDerivAt_id y)
    have huz : HasDerivAt (fun z : ℝ => 1 - z - lam) (0 - 1 - 0) y :=
      h1z.fun_sub (hasDerivAt_const y lam)
    have hprod := (hm2.fun_mul h1z).fun_mul huz
    refine hprod.congr_deriv ?_
    unfold foc
    have hb_ne : P.b ≠ 0 := P.hb.ne'
    have hy_ne : y ≠ 0 := hy_pos.ne'
    have h1y_ne : 1 - y ≠ 0 := h1y_pos.ne'
    have hu_ne : 1 - y - lam ≠ 0 := hu_pos.ne'
    field_simp [hb_ne, hy_ne, h1y_ne, hu_ne]
    ring
  have hLTilde_cont : ContinuousOn (LTilde P lam) (Set.Ioo 0 (1 - lam)) :=
    fun y hy => (hLTilde_deriv y hy).continuousAt.continuousWithinAt
  have hsub_Icc : Set.Icc x0 x ⊆ Set.Ioo 0 (1 - lam) :=
    fun y hy => ⟨hx0_pos.trans_le hy.1, hy.2.trans_lt hx.2⟩
  have hsub_Ico : Set.Ico x (1 - lam) ⊆ Set.Ioo 0 (1 - lam) :=
    fun y hy => ⟨hx.1.trans_le hy.1, hy.2⟩
  constructor
  · refine strictMonoOn_of_deriv_pos (convex_Icc x0 x) (hLTilde_cont.mono hsub_Icc) ?_
    rw [interior_Icc]
    intro y hy
    have hy_Ioo : y ∈ Set.Ioo 0 (1 - lam) := ⟨hx0_pos.trans hy.1, hy.2.trans hx.2⟩
    rw [(hLTilde_deriv y hy_Ioo).deriv]
    have hm_pos : 0 < mHat P y := by
      rw [← hmHat_x0]
      exact hmHat_mono ⟨hx0_pos, by linarith⟩ ⟨hy_Ioo.1, by linarith [hy_Ioo.2]⟩ hy.1
    have hu_pos : 0 < 1 - y - lam := by linarith [hy_Ioo.2]
    have hfoc_neg : foc P lam y < 0 := by
      rw [← hfoc]
      exact hfoc_mono hy_Ioo hx hy.2
    nlinarith [mul_pos hm_pos hu_pos]
  · refine strictAntiOn_of_deriv_neg (convex_Ico x (1 - lam)) (hLTilde_cont.mono hsub_Ico) ?_
    rw [interior_Ico]
    intro y hy
    have hy_Ioo : y ∈ Set.Ioo 0 (1 - lam) := ⟨hx.1.trans hy.1, hy.2⟩
    rw [(hLTilde_deriv y hy_Ioo).deriv]
    have hm_pos : 0 < mHat P y := by
      rw [← hmHat_x0]
      exact hmHat_mono ⟨hx0_pos, by linarith⟩ ⟨hy_Ioo.1, by linarith [hy_Ioo.2]⟩
        (hx0_lt_x.trans hy.1)
    have hu_pos : 0 < 1 - y - lam := by linarith [hy.2]
    have hfoc_pos : 0 < foc P lam y := by
      rw [← hfoc]
      exact hfoc_mono hx hy_Ioo hy.1
    nlinarith [mul_pos hm_pos hu_pos]
