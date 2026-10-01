-- Prove2me | solution 1 for SeasonalPricing.MyopicDet.revenue_le_at_tau2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:24:00.999251+00:00
-- url     : https://prove2.me/submissions/181a0f0e-ab4e-459c-961a-936974d68825

import Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
open MeasureTheory Set
open SeasonalPricing SeasonalPricing.MyopicDet

private theorem integral_initial (a b c : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, if x ≤ c then (1:ℝ) else 0) = max (min b c-a) 0 := by
  rw [intervalIntegral.integral_of_le hab]
  change (∫ x,(Iic c).indicator (fun _ : ℝ => (1:ℝ)) x ∂volume.restrict (Ioc a b)) = _
  rw [integral_indicator_const _ measurableSet_Iic,measureReal_restrict_apply measurableSet_Iic]
  have he : Iic c ∩ Ioc a b = Ioc a (min b c) := by ext x; simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]; tauto
  rw [he,Real.volume_real_Ioc]
  simp

private theorem price_time (ρ p t : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) :
    p*Real.exp (-Real.log ρ*t) ≤ 1 ↔ t ≤ tau ρ p := by
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  rw [←Real.log_le_log_iff (mul_pos hp (Real.exp_pos _)) (by norm_num : (0:ℝ)<1),
    Real.log_mul hp.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_one]
  unfold tau
  rw [le_div_iff_of_neg hl]
  constructor <;> intro h <;> nlinarith

private theorem tail_eq (ρ p t : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) :
    pointMassTail (p*Real.exp (-Real.log ρ*t)) = if t ≤ tau ρ p then 1 else 0 := by
  simp only [pointMassTail,price_time ρ p t hρ0 hρ1 hp]

private theorem tail_integrable (ρ p a b : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) :
    IntervalIntegrable (fun t => pointMassTail (p*Real.exp (-Real.log ρ*t))) volume a b := by
  simp only [tail_eq ρ p _ hρ0 hρ1 hp]
  rw [intervalIntegrable_iff']
  change Integrable ((Iic (tau ρ p)).indicator (fun _ : ℝ => (1:ℝ))) (volume.restrict (Icc (min a b) (max a b)))
  exact (integrable_const (1:ℝ)).indicator measurableSet_Iic

private theorem tail_integral (ρ p a b : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) (hab : a ≤ b) :
    (∫ t in a..b,pointMassTail (p*Real.exp (-Real.log ρ*t))) = max (min b (tau ρ p)-a) 0 := by
  simp only [tail_eq ρ p _ hρ0 hρ1 hp]
  exact integral_initial a b (tau ρ p) hab

private theorem waiting_tail (x y : ℝ) :
    pointMassTail (min x y)-pointMassTail x = if y ≤ 1 then 1-pointMassTail x else 0 := by
  unfold pointMassTail
  simp only [min_le_iff]
  split_ifs <;> grind

private theorem revenue_formula (lam ρ p1 p2 T : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    detRevenue lam ρ p1 p2 T = lam*(
      p1*max (min T (tau ρ p1)) 0 + p2*((if T ≤ tau ρ p2 then T-max (min T (tau ρ p1)) 0 else 0)
        +max (min 1 (tau ρ p2)-T) 0)) := by
  unfold detRevenue myopicRevenue Shared.LambdaI Shared.LambdaW Shared.LambdaL
  simp only [waiting_tail,price_time ρ p2 T hρ0 hρ1 hp2]
  split_ifs with hT
  · rw [intervalIntegral.integral_sub intervalIntegrable_const (tail_integrable ρ p1 0 T hρ0 hρ1 hp1),
      intervalIntegral.integral_const,tail_integral ρ p1 0 T hρ0 hρ1 hp1 hT0,
      tail_integral ρ p2 T 1 hρ0 hρ1 hp2 hT1]
    simp only [sub_zero,smul_eq_mul,mul_one]
    ring
  · rw [intervalIntegral.integral_zero,tail_integral ρ p1 0 T hρ0 hρ1 hp1 hT0,
      tail_integral ρ p2 T 1 hρ0 hρ1 hp2 hT1]
    simp only [sub_zero,mul_zero,zero_add]
    ring

private theorem tau_bounds (ρ p : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp0 : ρ ≤ p) (hp1 : p ≤ 1) :
    0 ≤ tau ρ p ∧ tau ρ p ≤ 1 := by
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hp : 0 < p := hρ0.trans_le hp0
  unfold tau
  constructor
  · exact div_nonneg_of_nonpos (Real.log_nonpos hp.le hp1) hl.le
  · rw [div_le_iff_of_neg hl,one_mul]
    exact Real.log_le_log hρ0 hp0

private theorem tau_antitone (ρ p1 p2 : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : 0 < p2) (hp12 : p2 ≤ p1) : tau ρ p1 ≤ tau ρ p2 := by
  unfold tau
  exact (div_le_div_right_of_neg (Real.log_neg hρ0 hρ1)).mpr (Real.log_le_log hp2 hp12)

private theorem revenue_middle (lam ρ p1 p2 T : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1)
    (hT1 : tau ρ p1 ≤ T) (hT2 : T ≤ tau ρ p2) :
    detRevenue lam ρ p1 p2 T = lam*reducedObjective ρ p1 p2 := by
  have ht1:=tau_bounds ρ p1 hρ0 hρ1 (hp2.trans hp12) hp1
  have ht2:=tau_bounds ρ p2 hρ0 hρ1 hp2 (hp12.trans hp1)
  rw [revenue_formula lam ρ p1 p2 T hρ0 hρ1 (hρ0.trans_le (hp2.trans hp12))
    (hρ0.trans_le hp2) (ht1.1.trans hT1) (hT2.trans ht2.2)]
  rw [min_eq_right hT1,max_eq_left ht1.1,if_pos hT2,min_eq_right ht2.2,
    max_eq_left (sub_nonneg.mpr hT2)]
  unfold reducedObjective tau
  ring

private theorem revenue_early (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1) (hT0 : 0 ≤ T) (hT : T ≤ tau ρ p1) :
    detRevenue lam ρ p1 p2 T ≤ detRevenue lam ρ p1 p2 (tau ρ p1) := by
  have ht1:=tau_bounds ρ p1 hρ0 hρ1 (hp2.trans hp12) hp1
  have ht2:=tau_bounds ρ p2 hρ0 hρ1 hp2 (hp12.trans hp1)
  have ht12:=tau_antitone ρ p1 p2 hρ0 hρ1 (hρ0.trans_le hp2) hp12
  rw [revenue_middle lam ρ p1 p2 (tau ρ p1) hρ0 hρ1 hp2 hp12 hp1 le_rfl ht12,
    revenue_formula lam ρ p1 p2 T hρ0 hρ1 (hρ0.trans_le (hp2.trans hp12))
      (hρ0.trans_le hp2) hT0 (hT.trans ht1.2),min_eq_left hT,max_eq_left hT0,
    if_pos (hT.trans ht12),min_eq_right ht2.2,max_eq_left (sub_nonneg.mpr (hT.trans ht12))]
  apply mul_le_mul_of_nonneg_left _ hlam.le
  have hh:=mul_nonneg (sub_nonneg.mpr hp12) (sub_nonneg.mpr hT)
  change _ ≤ (p1-p2)*tau ρ p1+p2*tau ρ p2
  nlinarith

private theorem revenue_late (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1) (hT : tau ρ p2 ≤ T) (hT1 : T ≤ 1) :
    detRevenue lam ρ p1 p2 T ≤ detRevenue lam ρ p1 p2 (tau ρ p2) := by
  have ht1:=tau_bounds ρ p1 hρ0 hρ1 (hp2.trans hp12) hp1
  have ht2:=tau_bounds ρ p2 hρ0 hρ1 hp2 (hp12.trans hp1)
  have ht12:=tau_antitone ρ p1 p2 hρ0 hρ1 (hρ0.trans_le hp2) hp12
  rcases hT.eq_or_lt with heq | hlt
  · rw [heq]
  rw [revenue_middle lam ρ p1 p2 (tau ρ p2) hρ0 hρ1 hp2 hp12 hp1 ht12 le_rfl,
    revenue_formula lam ρ p1 p2 T hρ0 hρ1 (hρ0.trans_le (hp2.trans hp12))
      (hρ0.trans_le hp2) (ht2.1.trans hT) hT1,min_eq_right (ht12.trans hT),max_eq_left ht1.1,
    if_neg (not_le.mpr hlt),min_eq_right ht2.2,max_eq_right (sub_nonpos.mpr hT)]
  apply mul_le_mul_of_nonneg_left _ hlam.le
  have hh:=mul_nonneg (hρ0.trans_le hp2).le (sub_nonneg.mpr ht12)
  change _ ≤ (p1-p2)*tau ρ p1+p2*tau ρ p2
  nlinarith


theorem solution (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1)
    (hT : tau ρ p2 ≤ T) (hT1 : T ≤ 1) :
    detRevenue lam ρ p1 p2 T ≤ detRevenue lam ρ p1 p2 (tau ρ p2) := by
  exact revenue_late lam ρ p1 p2 T hlam hρ0 hρ1 hp2 hp12 hp1 hT hT1
