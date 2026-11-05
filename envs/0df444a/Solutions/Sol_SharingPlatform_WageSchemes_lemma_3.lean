-- Prove2me | solution 1 for SharingPlatform.WageSchemes.lemma_3
-- status  : ACCEPTED   (disprove)
-- author  : @frknbls
-- created : 2026-11-04T13:54:28.35294+00:00
-- url     : https://prove2.me/submissions/642043e0-5e9f-4a25-aed7-e7e333ef51c9

import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

/-- Profit rewritten with demand in the form `A - B p`. -/
lemma spwd_prof_eq (P : Params) (p w q v : ℝ) :
    profit P p w q v =
      (p - w) * max 0 (min ((P.a + P.b * q) - (P.b + P.c) * p) (supply P w v)) := by
  unfold profit volume demand
  rw [show P.a - P.b * (p - q) - P.c * p = (P.a + P.b * q) - (P.b + P.c) * p by ring]

/-- A best response never prices strictly below the kink `(A - s)/B` when supply is positive. -/
lemma spwd_lb_kink {A B w s p : ℝ} (hB : 0 < B) (hs : 0 < s)
    (h : ∀ p', (p' - w) * max 0 (min (A - B * p') s) ≤ (p - w) * max 0 (min (A - B * p) s)) :
    (A - s) / B ≤ p := by
  by_contra hlt
  push Not at hlt
  have h1 : A - B * ((A - s) / B) = s := by field_simp; ring
  have h2 : s < A - B * p := by
    have := (lt_div_iff₀ hB).mp hlt
    linarith
  have h3 := h ((A - s) / B)
  rw [h1, min_self, max_eq_right hs.le, min_eq_right h2.le, max_eq_right hs.le] at h3
  have := le_of_mul_le_mul_right h3 hs
  linarith

/-- A best response never prices strictly below the unconstrained optimum when the
unconstrained margin is positive and supply is positive. -/
lemma spwd_lb_unc {A B w s p : ℝ} (hB : 0 < B) (hs : 0 < s) (hA : 0 < A - B * w)
    (h : ∀ p', (p' - w) * max 0 (min (A - B * p') s) ≤ (p - w) * max 0 (min (A - B * p) s)) :
    (A + B * w) / (2 * B) ≤ p := by
  have hk := spwd_lb_kink hB hs h
  by_contra hlt
  push Not at hlt
  have hk' : A - s ≤ B * p := by have := (div_le_iff₀ hB).mp hk; linarith
  have hu : B * p * 2 < A + B * w := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * B)).mp hlt
    linarith
  set pu := (A + B * w) / (2 * B) with hpu
  have hpu1 : A - B * pu = (A - B * w) / 2 := by rw [hpu]; field_simp; ring
  have hpu2 : pu - w = (A - B * w) / (2 * B) := by rw [hpu]; field_simp; ring
  have hle : A - B * pu ≤ s := by
    have : 2 * (B * pu) = A + B * w := by rw [hpu]; field_simp
    linarith
  have h3 := h pu
  rw [min_eq_left hle, max_eq_right (by rw [hpu1]; linarith), hpu1, hpu2] at h3
  have hval : 0 < (A - B * w) / (2 * B) * ((A - B * w) / 2) := by positivity
  -- bound the right side
  have hV0 : 0 ≤ max 0 (min (A - B * p) s) := le_max_left _ _
  rcases le_or_gt p w with hpw | hpw
  · have : (p - w) * max 0 (min (A - B * p) s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0
    linarith
  · rcases le_or_gt (A - B * p) 0 with hd | hd
    · have : max 0 (min (A - B * p) s) = 0 :=
        max_eq_left (le_trans (min_le_left _ _) hd)
      rw [this] at h3
      linarith
    · have hm : max 0 (min (A - B * p) s) ≤ A - B * p :=
        max_le hd.le (min_le_left _ _)
      have h4 : (p - w) * max 0 (min (A - B * p) s) ≤ (p - w) * (A - B * p) :=
        mul_le_mul_of_nonneg_left hm (by linarith)
      have h5 : (p - w) * (A - B * p) < (A - B * w) / (2 * B) * ((A - B * w) / 2) := by
        have e : (A - B * w) / (2 * B) * ((A - B * w) / 2) - (p - w) * (A - B * p)
            = (A + B * w - 2 * B * p) ^ 2 / (4 * B) := by field_simp; ring
        have : 0 < (A + B * w - 2 * B * p) ^ 2 / (4 * B) := by
          apply div_pos _ (by positivity)
          have : 0 < A + B * w - 2 * B * p := by linarith
          positivity
        linarith
      linarith

/-- The counterexample parameters. -/
noncomputable def spwdP : Params := ⟨5, 1/20, 1, 1, 21, 1/2⟩

lemma spwd_standing : spwdP.Standing := by
  unfold Params.Standing spwdP
  norm_num

lemma spwd_wW : wW spwdP = 13162 / 3743 := by
  unfold wW spwdP
  norm_num

lemma spwd_pW : pW spwdP = 15877 / 3743 := by
  unfold pW
  rw [spwd_wW]
  unfold spwdP
  norm_num

theorem _root_.solution : ¬ (∀ (P : Params) (hP : P.Standing),
    (∃ e : TwoStage, IsSPE P fwWage e ∧ e.OnPathContinuous ∧ e.IsSymmetric ∧
      e.Nontrivial P fwWage ∧ e.x₁ = wW P ∧ e.P₁ e.x₁ e.x₂ = pW P) ∧
    (∀ e : TwoStage, IsSPE P fwWage e → e.OnPathContinuous → e.IsSymmetric →
      e.Nontrivial P fwWage → e.x₁ = wW P ∧ e.P₁ e.x₁ e.x₂ = pW P)) := by
  intro H
  obtain ⟨⟨e, hspe, -, ⟨hsym1, hsym2⟩, -, hx1, hp1⟩, -⟩ := H spwdP spwd_standing
  rw [spwd_wW] at hx1
  rw [spwd_pW] at hp1
  have hx2 : e.x₂ = 13162 / 3743 := by rw [← hsym1, hx1]
  set y : ℝ := 13158257 / 3743000 with hy
  -- stage-1 deviation of platform 1
  have hdev := hspe.2.1 y
  unfold TwoStage.profit₁ at hdev
  simp only [fwWage] at hdev
  rw [← hsym2, hp1, hx1, hx2] at hdev
  -- on-path profit
  have hbase : profit spwdP (15877 / 3743) (13162 / 3743) (15877 / 3743) (13162 / 3743)
      = 7705170 / 14010049 := by
    rw [spwd_prof_eq]
    unfold supply spwdP
    norm_num [min_def, max_def]
  rw [hbase] at hdev
  -- pricing Nash in the deviation subgame
  obtain ⟨hN1, hN2⟩ := hspe.1 y e.x₂
  rw [hx2] at hN1 hN2
  set q1 := e.P₁ y (13162 / 3743) with hq1
  set q2 := e.P₂ y (13162 / 3743) with hq2
  simp only [fwWage, spwd_prof_eq] at hN1 hN2
  have hs1 : supply spwdP y (13162 / 3743) = 5515051 / 7486000 := by
    unfold supply spwdP; rw [hy]; norm_num
  have hs2 : supply spwdP (13162 / 3743) y = 2916603 / 3743000 := by
    unfold supply spwdP; rw [hy]; norm_num
  rw [hs1] at hN1
  rw [hs2] at hN2
  have ha : spwdP.a = 5 := rfl
  have hb : spwdP.b = 1 / 20 := rfl
  have hc : spwdP.c = 1 := rfl
  rw [ha, hb, hc] at hN1 hN2
  have K1 := spwd_lb_kink (by norm_num) (by norm_num) hN1
  have K2 := spwd_lb_kink (by norm_num) (by norm_num) hN2
  have K1' : 5 + 1 / 20 * q2 - 5515051 / 7486000 ≤ (1 / 20 + 1) * q1 := by
    have := K1; rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 20 + 1)] at this; linarith
  have K2' : 5 + 1 / 20 * q1 - 2916603 / 3743000 ≤ (1 / 20 + 1) * q2 := by
    have := K2; rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 20 + 1)] at this; linarith
  have hA2 : 0 < 5 + 1 / 20 * q1 - (1 / 20 + 1) * (13162 / 3743 : ℝ) := by linarith
  have U2 := spwd_lb_unc (by norm_num) (by norm_num) hA2 hN2
  have U2' : 5 + 1 / 20 * q1 + (1 / 20 + 1) * (13162 / 3743 : ℝ) ≤
      2 * (1 / 20 + 1) * q2 := by
    have := U2; rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2 * (1 / 20 + 1))] at this; linarith
  have L1 : (36986791 / 8677850 : ℝ) ≤ q1 := by linarith
  have L2 : (1398389149 / 329758300 : ℝ) ≤ q2 := by linarith
  -- platform 1 could price at the lower bound
  have h3 := hN1 (36986791 / 8677850)
  have hdem : 5515051 / 7486000 ≤ 5 + 1 / 20 * q2 - (1 / 20 + 1) * (36986791 / 8677850 : ℝ) := by
    linarith
  rw [min_eq_right hdem, max_eq_right (by norm_num)] at h3
  rw [spwd_prof_eq, hs1, ha, hb, hc] at hdev
  have : (13581122829309313 / 24685706338000000 : ℝ) ≤ 7705170 / 14010049 := by
    have e1 : ((36986791 / 8677850 : ℝ) - y) * (5515051 / 7486000)
        = 13581122829309313 / 24685706338000000 := by rw [hy]; norm_num
    linarith
  norm_num at this

end SharingPlatform.WageSchemes
