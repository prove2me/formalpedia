-- Prove2me | solution 1 for RiskPostpone.Threshold.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:35:44.876996+00:00
-- url     : https://prove2.me/submissions/2053af7f-29e5-4bd3-bb0c-6d34f410a7c9

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RiskPostpone_Threshold_CVaR
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace Aux_RPTl1

lemma conc_mono (r : ℝ → ℝ) (D ds : ℝ) (hconc : ConcaveOn ℝ (Icc 0 D) r) (hds : ds ∈ Icc 0 D)
    (hmax : IsMaxOn r (Icc 0 D) ds) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ds) :
    r a ≤ r b := by
  have haI : a ∈ Icc 0 D := ⟨ha, (hab.trans hb).trans hds.2⟩
  have hm : r a ≤ r ds := isMaxOn_iff.1 hmax a haI
  rcases eq_or_lt_of_le (hab.trans hb) with h | h
  · have hb' : b = ds := le_antisymm hb (h ▸ hab)
    rw [hb', ← h]
  · set t := (ds - b) / (ds - a) with ht
    have hpos : 0 < ds - a := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
    have hb_eq : t * a + (1 - t) * ds = b := by
      rw [ht]; field_simp; ring
    have := hconc.2 haI hds ht0 (by linarith : 0 ≤ 1 - t) (by ring)
    simp only [smul_eq_mul] at this
    rw [hb_eq] at this
    nlinarith

end Aux_RPTl1

open RiskPostpone.Threshold Aux_RPTl1 in
theorem solution (M : Model) (hM : M.Standing) (hA2 : M.Assumption2) (dstar : ℝ)
    (hds : dstar ∈ Icc 0 (M.d 0)) (hmax : IsMaxOn (fun x => M.P x * x) (Icc 0 (M.d 0)) dstar)
    (q ξ : ℝ) (hq : 0 ≤ q) (hξ : 0 ≤ ξ) :
    M.P (min (q * ξ) dstar) ∈ Icc 0 M.p0 ∧
    M.P (min (q * ξ) dstar) * min (M.d (M.P (min (q * ξ) dstar))) (q * ξ) =
      min (q * ξ) dstar * M.P (min (q * ξ) dstar) ∧
    IsGreatest ((fun p => p * min (M.d p) (q * ξ)) '' Icc 0 M.p0)
      (min (q * ξ) dstar * M.P (min (q * ξ) dstar)) := by
  have hp0 := hM.p0_pos
  have hPr : ∀ y ∈ Icc 0 (M.d 0), M.P y ∈ Icc 0 M.p0 := by
    intro y hy
    obtain ⟨p, hp, hdp⟩ := intermediate_value_Icc' hp0.le hM.d_cont
      (⟨by rw [hM.d_p0]; exact hy.1, hy.2⟩ : y ∈ Icc (M.d M.p0) (M.d 0))
    rw [← hdp, hM.P_d p hp]
    exact hp
  have hdr : ∀ p ∈ Icc 0 M.p0, M.d p ∈ Icc 0 (M.d 0) := by
    intro p hp
    have hanti := hM.d_strictAnti.antitoneOn
    exact ⟨by rw [← hM.d_p0]; exact hanti hp ⟨hp0.le, le_rfl⟩ hp.2,
      hanti ⟨le_rfl, hp0.le⟩ hp hp.1⟩
  have hqξ : 0 ≤ q * ξ := mul_nonneg hq hξ
  set x := min (q * ξ) dstar with hx
  have hxI : x ∈ Icc 0 (M.d 0) := ⟨le_min hqξ hds.1, (min_le_right _ _).trans hds.2⟩
  have c1 : M.P x ∈ Icc 0 M.p0 := hPr x hxI
  have hdPx : M.d (M.P x) = x := hM.d_P x hxI
  have c2 : M.P x * min (M.d (M.P x)) (q * ξ) = x * M.P x := by
    rw [hdPx, min_eq_left (min_le_left _ _)]; ring
  refine ⟨c1, c2, ⟨⟨M.P x, c1, by simp only; rw [c2]⟩, ?_⟩⟩
  rintro _ ⟨p, hp, rfl⟩
  simp only
  set r : ℝ → ℝ := fun y => M.P y * y with hr
  have hrmax : ∀ y ∈ Icc 0 (M.d 0), r y ≤ r dstar := fun y hy => isMaxOn_iff.1 hmax y hy
  have hrx : x * M.P x = r x := by rw [hr]; ring
  rw [hrx]
  -- r y ≤ r x for y ∈ [0, d0] with y ≤ q ξ
  have key : ∀ y ∈ Icc 0 (M.d 0), y ≤ q * ξ → r y ≤ r x := by
    intro y hy hyq
    rcases le_total y dstar with h | h
    · exact conc_mono r (M.d 0) dstar hA2 hds hmax y x hy.1 (le_min hyq h) (min_le_right _ _)
    · have : x = dstar := by
        rw [hx]; exact min_eq_right (h.trans hyq)
      rw [this]; exact hrmax y hy
  rcases le_total (M.d p) (q * ξ) with h | h
  · rw [min_eq_left h]
    have hdp := hdr p hp
    have e : p * M.d p = r (M.d p) := by rw [hr]; simp only; rw [hM.P_d p hp]
    rw [e]
    exact key _ hdp h
  · rw [min_eq_right h]
    have hqI : q * ξ ∈ Icc 0 (M.d 0) := ⟨hqξ, h.trans (hdr p hp).2⟩
    have hPq := hPr _ hqI
    have hle : p ≤ M.P (q * ξ) := by
      by_contra hc
      push Not at hc
      have := hM.d_strictAnti hPq hp hc
      rw [hM.d_P _ hqI] at this
      linarith
    calc p * (q * ξ) ≤ M.P (q * ξ) * (q * ξ) := mul_le_mul_of_nonneg_right hle hqξ
      _ = r (q * ξ) := rfl
      _ ≤ r x := key _ hqI le_rfl
