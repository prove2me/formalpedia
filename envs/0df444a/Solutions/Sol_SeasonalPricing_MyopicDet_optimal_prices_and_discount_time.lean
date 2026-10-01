-- Prove2me | solution 1 for SeasonalPricing.MyopicDet.optimal_prices_and_discount_time
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:26:29.406995+00:00
-- url     : https://prove2.me/submissions/2d6e50c8-bec1-411b-9360-e75679584da7

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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

private theorem revenue_envelope (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : 0 < p2) (hp12 : p2 ≤ p1) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    detRevenue lam ρ p1 p2 T ≤ lam*((p1-p2)*max (min 1 (tau ρ p1)) 0
      +p2*max (min 1 (tau ρ p2)) 0) := by
  have ht12:=tau_antitone ρ p1 p2 hρ0 hρ1 hp2 hp12
  rw [revenue_formula lam ρ p1 p2 T hρ0 hρ1 (hp2.trans_le hp12) hp2 hT0 hT1]
  apply mul_le_mul_of_nonneg_left _ hlam.le
  by_cases hT : T ≤ tau ρ p2
  · rw [if_pos hT,max_eq_left (sub_nonneg.mpr (le_min hT1 hT)),
      max_eq_left (hT0.trans (le_min hT1 hT))]
    have hA : max (min T (tau ρ p1)) 0 ≤ max (min 1 (tau ρ p1)) 0 :=
      max_le_max (min_le_min hT1 le_rfl) le_rfl
    have hh:=mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hp12)
    nlinarith
  · have hT' : tau ρ p2 < T := lt_of_not_ge hT
    have ht1 : tau ρ p1 ≤ 1 := (ht12.trans hT'.le).trans hT1
    have ht2 : tau ρ p2 ≤ 1 := hT'.le.trans hT1
    rw [if_neg hT,min_eq_right (ht12.trans hT'.le),min_eq_right ht1,
      min_eq_right ht2,max_eq_right (sub_nonpos.mpr hT'.le)]
    have hh:=mul_le_mul_of_nonneg_left (max_le_max ht12 (show (0:ℝ)≤0 from le_rfl)) hp2.le
    nlinarith

private theorem clipped_time (ρ p : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) :
    (p ≤ ρ → max (min 1 (tau ρ p)) 0=1) ∧
    (1 ≤ p → max (min 1 (tau ρ p)) 0=0) := by
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  constructor
  · intro hpr
    have ht : 1 ≤ tau ρ p := by
      unfold tau
      rw [le_div_iff_of_neg hl,one_mul]
      exact Real.log_le_log hp hpr
    rw [min_eq_left ht,max_eq_left (by norm_num : (0:ℝ)≤1)]
  · intro hp1
    have ht : tau ρ p ≤ 0 := div_nonpos_of_nonneg_of_nonpos (Real.log_nonneg hp1) hl.le
    rw [min_eq_right (ht.trans (by norm_num)),max_eq_right ht]

private theorem revenue_dominated (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : 0 < p2) (hp12 : p2 ≤ p1) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∃ q1 q2,ρ ≤ q2 ∧ q2 ≤ q1 ∧ q1 ≤ 1 ∧ detRevenue lam ρ p1 p2 T ≤ lam*reducedObjective ρ q1 q2 := by
  have hp1:=hp2.trans_le hp12
  have hb:=revenue_envelope lam ρ p1 p2 T hlam hρ0 hρ1 hp2 hp12 hT0 hT1
  have hr : tau ρ ρ=1 := by unfold tau; exact div_self (Real.log_neg hρ0 hρ1).ne
  have hrr : reducedObjective ρ ρ ρ=ρ := by change (ρ-ρ)*tau ρ ρ+ρ*tau ρ ρ=ρ; simp [hr]
  have hsingle : ∀ p,reducedObjective ρ p p=p*tau ρ p := by intro p; unfold reducedObjective tau; ring
  by_cases hp1r : p1 ≤ ρ
  · refine ⟨ρ,ρ,le_rfl,le_rfl,hρ1.le,?_⟩
    rw [(clipped_time ρ p1 hρ0 hρ1 hp1).1 hp1r,
      (clipped_time ρ p2 hρ0 hρ1 hp2).1 (hp12.trans hp1r)] at hb
    rw [hrr]
    have hh:=mul_le_mul_of_nonneg_left hp1r hlam.le
    nlinarith
  · by_cases hp11 : 1 ≤ p1
    · rw [(clipped_time ρ p1 hρ0 hρ1 hp1).2 hp11,mul_zero,zero_add] at hb
      by_cases hp2r : p2 ≤ ρ
      · refine ⟨ρ,ρ,le_rfl,le_rfl,hρ1.le,?_⟩
        rw [(clipped_time ρ p2 hρ0 hρ1 hp2).1 hp2r,mul_one] at hb
        rw [hrr]
        exact hb.trans (mul_le_mul_of_nonneg_left hp2r hlam.le)
      · by_cases hp21 : 1 ≤ p2
        · refine ⟨ρ,ρ,le_rfl,le_rfl,hρ1.le,?_⟩
          rw [(clipped_time ρ p2 hρ0 hρ1 hp2).2 hp21,mul_zero,mul_zero] at hb
          rw [hrr]
          exact hb.trans (mul_nonneg hlam.le hρ0.le)
        · have ht:=tau_bounds ρ p2 hρ0 hρ1 (le_of_not_ge hp2r) (le_of_not_ge hp21)
          refine ⟨p2,p2,le_of_not_ge hp2r,le_rfl,le_of_not_ge hp21,?_⟩
          rw [min_eq_right ht.2,max_eq_left ht.1] at hb
          rwa [hsingle]
    · have hp1r' : ρ ≤ p1 := le_of_not_ge hp1r
      have hp11' : p1 ≤ 1 := le_of_not_ge hp11
      have ht1:=tau_bounds ρ p1 hρ0 hρ1 hp1r' hp11'
      rw [min_eq_right ht1.2,max_eq_left ht1.1] at hb
      by_cases hp2r : p2 ≤ ρ
      · refine ⟨p1,ρ,le_rfl,hp1r',hp11',?_⟩
        rw [(clipped_time ρ p2 hρ0 hρ1 hp2).1 hp2r,mul_one] at hb
        have hh:=mul_nonneg (sub_nonneg.mpr hp2r) (sub_nonneg.mpr ht1.2)
        change _ ≤ lam*((p1-ρ)*tau ρ p1+ρ*tau ρ ρ)
        rw [hr,mul_one]
        have hbound : (p1-p2)*tau ρ p1+p2 ≤ (p1-ρ)*tau ρ p1+ρ := by nlinarith
        exact hb.trans (mul_le_mul_of_nonneg_left hbound hlam.le)
      · have ht2:=tau_bounds ρ p2 hρ0 hρ1 (le_of_not_ge hp2r) (hp12.trans hp11')
        rw [min_eq_right ht2.2,max_eq_left ht2.1] at hb
        exact ⟨p1,p2,le_of_not_ge hp2r,hp12,hp11',hb⟩


private theorem price_rpow_time (ρ p T : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) :
    (p ≤ ρ^T ↔ T ≤ tau ρ p) ∧ (ρ^T ≤ p ↔ tau ρ p ≤ T) := by
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  constructor
  · rw [←Real.log_le_log_iff hp (Real.rpow_pos_of_pos hρ0 _),Real.log_rpow hρ0]
    unfold tau
    rw [le_div_iff_of_neg hl]
  · rw [←Real.log_le_log_iff (Real.rpow_pos_of_pos hρ0 _) hp,Real.log_rpow hρ0]
    unfold tau
    rw [div_le_iff_of_neg hl]

private theorem reduced_maximum (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ M,IsGreatest {g : ℝ | ∃ p1 p2 : ℝ,ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧ g=reducedObjective ρ p1 p2} M := by
  let D : Set (ℝ×ℝ) := (Icc ρ 1 ×ˢ Icc ρ 1) ∩ {p | p.2 ≤ p.1}
  have hc : IsCompact D := (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_snd continuous_fst)
  have hn : D.Nonempty := ⟨(ρ,ρ),by simp [D,hρ1.le]⟩
  have hf : ContinuousOn (fun p : ℝ×ℝ => reducedObjective ρ p.1 p.2) D := by
    intro p hp
    have h1 : p.1 ≠ 0 := (hρ0.trans_le hp.1.1.1).ne'
    have h2 : p.2 ≠ 0 := (hρ0.trans_le hp.1.2.1).ne'
    have hl : Real.log ρ ≠ 0 := (Real.log_neg hρ0 hρ1).ne
    apply ContinuousAt.continuousWithinAt
    unfold reducedObjective
    fun_prop
  obtain ⟨p,hp,hmax⟩:=hc.exists_isMaxOn hn hf
  refine ⟨reducedObjective ρ p.1 p.2,⟨?_,?_⟩⟩
  · exact ⟨p.1,p.2,hp.1.2.1,hp.2,hp.1.1.2,rfl⟩
  · rintro g ⟨q1,q2,hq2,hq12,hq1,rfl⟩
    exact hmax (show (q1,q2) ∈ D from ⟨⟨⟨hq2.trans hq12,hq1⟩,⟨hq2,hq12.trans hq1⟩⟩,hq12⟩)

private theorem revenue_maximum (lam ρ M : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hM : IsGreatest {g : ℝ | ∃ p1 p2 : ℝ,ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧ g=reducedObjective ρ p1 p2} M) :
    IsGreatest {r : ℝ | ∃ p1 p2 T : ℝ,0 < p2 ∧ p2 ≤ p1 ∧ 0 ≤ T ∧ T ≤ 1 ∧ r=detRevenue lam ρ p1 p2 T} (lam*M) := by
  constructor
  · obtain ⟨p1,p2,hp2,hp12,hp1,hMp⟩:=hM.1
    have ht1:=tau_bounds ρ p1 hρ0 hρ1 (hp2.trans hp12) hp1
    have ht12:=tau_antitone ρ p1 p2 hρ0 hρ1 (hρ0.trans_le hp2) hp12
    refine ⟨p1,p2,tau ρ p1,hρ0.trans_le hp2,hp12,ht1.1,ht1.2,?_⟩
    rw [revenue_middle lam ρ p1 p2 (tau ρ p1) hρ0 hρ1 hp2 hp12 hp1 le_rfl ht12,hMp]
  · rintro r ⟨p1,p2,T,hp2,hp12,hT0,hT1,rfl⟩
    obtain ⟨q1,q2,hq2,hq12,hq1,hb⟩:=revenue_dominated lam ρ p1 p2 T hlam hρ0 hρ1 hp2 hp12 hT0 hT1
    exact hb.trans (mul_le_mul_of_nonneg_left (hM.2 ⟨q1,q2,hq2,hq12,hq1,rfl⟩) hlam.le)
open Set
open SeasonalPricing.MyopicDet

private theorem log_minimum (C x : ℝ) (hx : 0 < x) :
    -Real.exp (C-1) ≤ x*(Real.log x-C) ∧
      (x*(Real.log x-C) = -Real.exp (C-1) → x=Real.exp (C-1)) := by
  let q := Real.exp (C-1)
  have hq : 0 < q := Real.exp_pos _
  have he : q*((x/q)*Real.log (x/q)-(x/q)+1)=x*(Real.log x-C)+q := by
    rw [Real.log_div hx.ne' hq.ne']
    rw [show Real.log q=C-1 from Real.log_exp _]
    field_simp
    ring
  have h1:=Real.self_sub_one_le_mul_log (div_pos hx hq).le
  have h2:=mul_nonneg hq.le (sub_nonneg.mpr h1)
  have hl : -q ≤ x*(Real.log x-C) := by nlinarith
  refine ⟨hl,?_⟩
  intro hh
  by_contra hne
  have hne' : x/q ≠ 1 := by intro heq; apply hne; exact (div_eq_one_iff_eq hq.ne').mp heq
  have h3:=Real.self_sub_one_lt_mul_log (div_pos hx hq).le hne'
  have h4:=mul_pos hq (sub_pos.mpr h3)
  change x*(Real.log x-C) = -q at hh
  nlinarith

private theorem numerator_bound (p1 p2 : ℝ) (h1 : 0 < p1) (h2 : 0 < p2) :
    -Real.exp (-1+Real.exp (-1)) ≤ (p1-p2)*Real.log p1+p2*Real.log p2 ∧
    ((p1-p2)*Real.log p1+p2*Real.log p2 = -Real.exp (-1+Real.exp (-1)) →
      p1=Real.exp (-1+Real.exp (-1)) ∧ p2=p1/Real.exp 1) := by
  let r := p2/p1
  have hr : 0 < r := div_pos h2 h1
  have hminr:=log_minimum 0 r hr
  have hminp:=log_minimum (Real.exp (-1)) p1 h1
  simp only [sub_zero,zero_sub] at hminr
  rw [show Real.exp (-1)-1 = -1+Real.exp (-1) by ring] at hminp
  have he : (p1-p2)*Real.log p1+p2*Real.log p2 = p1*(Real.log p1+r*Real.log r) := by
    dsimp [r]
    rw [Real.log_div h2.ne' h1.ne']
    field_simp
    ring
  have hh:=mul_le_mul_of_nonneg_left hminr.1 h1.le
  have hl : -Real.exp (-1+Real.exp (-1)) ≤ (p1-p2)*Real.log p1+p2*Real.log p2 := by
    rw [he]
    nlinarith [hminp.1]
  refine ⟨hl,?_⟩
  intro heq
  rw [he] at heq
  have hpEq : p1*(Real.log p1-Real.exp (-1)) = -Real.exp (-1+Real.exp (-1)) := by
    nlinarith [hminp.1]
  have hrEq : r*Real.log r = -Real.exp (-1) := by nlinarith
  have hp:=hminp.2 hpEq
  have hr':=hminr.2 hrEq
  refine ⟨hp,?_⟩
  dsimp [r] at hr'
  rw [Real.exp_neg] at hr'
  have heq := (div_eq_iff h1.ne').mp hr'
  simpa [div_eq_mul_inv,mul_comm] using heq

private theorem optimum_values :
    (0 < Real.exp (-1+Real.exp (-1))) ∧
    (Real.exp (-1+Real.exp (-1)) ≤ 1) ∧
    (Real.exp (-1+Real.exp (-1))/Real.exp 1 = Real.exp (-2+Real.exp (-1))) ∧
    (Real.exp (-1+Real.exp (-1))/Real.exp 1 ≤ Real.exp (-1+Real.exp (-1))) := by
  have he : Real.exp (-1) < 1 := by exact Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (by linarith),?_,?_⟩
  · rw [←Real.exp_sub]
    congr 1
    ring
  · exact div_le_self (Real.exp_pos _).le (Real.one_le_exp_iff.mpr (by norm_num))

private theorem optimal_numerator :
    (Real.exp (-1+Real.exp (-1))-Real.exp (-1+Real.exp (-1))/Real.exp 1)*Real.log (Real.exp (-1+Real.exp (-1)))
      +(Real.exp (-1+Real.exp (-1))/Real.exp 1)*Real.log (Real.exp (-1+Real.exp (-1))/Real.exp 1)
      = -Real.exp (-1+Real.exp (-1)) := by
  rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
  rw [Real.exp_neg]
  field_simp
  ring

private theorem special_case (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ Real.exp (-2 + Real.exp (-1))) :
    IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧ g = reducedObjective ρ p1 p2}
        (-Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      ρ ≤ Real.exp (-1 + Real.exp (-1)) / Real.exp 1 ∧
      Real.exp (-1 + Real.exp (-1)) ≤ 1 ∧
      reducedObjective ρ (Real.exp (-1 + Real.exp (-1)))
          (Real.exp (-1 + Real.exp (-1)) / Real.exp 1) =
        -Real.exp (-1 + Real.exp (-1)) / Real.log ρ ∧
      ∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 →
        reducedObjective ρ p1 p2 = -Real.exp (-1 + Real.exp (-1)) / Real.log ρ →
          p1 = Real.exp (-1 + Real.exp (-1)) ∧ p2 = Real.exp (-1 + Real.exp (-1)) / Real.exp 1 := by
  obtain ⟨hp0,hp1,heq,hp12⟩:=optimum_values
  have hp2 : ρ ≤ Real.exp (-1+Real.exp (-1))/Real.exp 1 := by rwa [heq]
  have hρ1 : ρ < 1 := by
    have hh : Real.exp (-2+Real.exp (-1)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ)<0)])
    exact hρ.trans_lt hh
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hid : ∀ p1 p2,reducedObjective ρ p1 p2 =
      ((p1-p2)*Real.log p1+p2*Real.log p2)/Real.log ρ := by
    intro p1 p2
    unfold reducedObjective
    ring
  have hop : reducedObjective ρ (Real.exp (-1+Real.exp (-1)))
      (Real.exp (-1+Real.exp (-1))/Real.exp 1) = -Real.exp (-1+Real.exp (-1))/Real.log ρ := by
    rw [hid,optimal_numerator]
  refine ⟨⟨?_,?_⟩,hp2,hp1,hop,?_⟩
  · exact ⟨_,_,hp2,hp12,hp1,hop.symm⟩
  · rintro g ⟨p1,p2,hp2',hp12',hp1',rfl⟩
    rw [hid]
    exact (div_le_div_right_of_neg hl).mpr (numerator_bound p1 p2
      (hρ0.trans_le (hp2'.trans hp12')) (hρ0.trans_le hp2')).1
  · intro p1 p2 hp2' hp12' hp1' hop'
    rw [hid] at hop'
    have he := (div_left_inj' hl.ne).mp hop'
    obtain ⟨h1,h2⟩:=(numerator_bound p1 p2 (hρ0.trans_le (hp2'.trans hp12'))
      (hρ0.trans_le hp2')).2 he
    exact ⟨h1,by simpa [h1] using h2⟩
theorem solution (lam ρ : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    (∃ M : ℝ,
      IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧
          g = reducedObjective ρ p1 p2} M ∧
      IsGreatest {r : ℝ | ∃ p1 p2 T : ℝ, 0 < p2 ∧ p2 ≤ p1 ∧ 0 ≤ T ∧ T ≤ 1 ∧
          r = detRevenue lam ρ p1 p2 T} (lam * M) ∧
      ∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 → reducedObjective ρ p1 p2 = M →
        ∀ T : ℝ, p2 ≤ ρ ^ T → ρ ^ T ≤ p1 → detRevenue lam ρ p1 p2 T = lam * M) ∧
    (ρ ≤ Real.exp (-2 + Real.exp (-1)) →
      IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧
          g = reducedObjective ρ p1 p2} (-Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      (∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 →
        reducedObjective ρ p1 p2 = -Real.exp (-1 + Real.exp (-1)) / Real.log ρ →
          p1 = Real.exp (-1 + Real.exp (-1)) ∧
            p2 = Real.exp (-1 + Real.exp (-1)) / Real.exp 1) ∧
      IsGreatest {r : ℝ | ∃ p1 p2 T : ℝ, 0 < p2 ∧ p2 ≤ p1 ∧ 0 ≤ T ∧ T ≤ 1 ∧
          r = detRevenue lam ρ p1 p2 T} (-lam * Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      ∀ T : ℝ, Real.exp (-2 + Real.exp (-1)) ≤ ρ ^ T → ρ ^ T ≤ Real.exp (-1 + Real.exp (-1)) →
        detRevenue lam ρ (Real.exp (-1 + Real.exp (-1)))
            (Real.exp (-1 + Real.exp (-1)) / Real.exp 1) T =
          -lam * Real.exp (-1 + Real.exp (-1)) / Real.log ρ) := by
  constructor
  · obtain ⟨M,hM⟩:=reduced_maximum ρ hρ0 hρ1
    refine ⟨M,hM,revenue_maximum lam ρ M hlam hρ0 hρ1 hM,?_⟩
    intro p1 p2 hp2 hp12 hp1 hop T hTp2 hTp1
    have ht1 := (price_rpow_time ρ p1 T hρ0 hρ1 (hρ0.trans_le (hp2.trans hp12))).2.mp hTp1
    have ht2 := (price_rpow_time ρ p2 T hρ0 hρ1 (hρ0.trans_le hp2)).1.mp hTp2
    rw [revenue_middle lam ρ p1 p2 T hρ0 hρ1 hp2 hp12 hp1 ht1 ht2,hop]
  · intro hρ
    obtain ⟨hM,hp2,hp1,hop,hunique⟩:=special_case ρ hρ0 hρ
    refine ⟨hM,hunique,?_,?_⟩
    · have hh:=revenue_maximum lam ρ (-Real.exp (-1+Real.exp (-1))/Real.log ρ) hlam hρ0 hρ1 hM
      convert hh using 1 <;> ring
    · intro T hTlo hThi
      obtain ⟨hpos,hle,heq,hp12⟩:=optimum_values
      have hTlo' : Real.exp (-1+Real.exp (-1))/Real.exp 1 ≤ ρ^T := by rwa [heq]
      have ht1 := (price_rpow_time ρ (Real.exp (-1+Real.exp (-1))) T hρ0 hρ1 hpos).2.mp hThi
      have ht2 := (price_rpow_time ρ (Real.exp (-1+Real.exp (-1))/Real.exp 1) T hρ0 hρ1
        (div_pos hpos (Real.exp_pos _))).1.mp hTlo'
      rw [revenue_middle lam ρ _ _ T hρ0 hρ1 hp2 hp12 hp1 ht1 ht2,hop]
      ring
