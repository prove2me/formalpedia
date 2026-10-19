-- Prove2me | solution 1 for PPDifferentiation.ShortRun.asymmetric_profits
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:53:58.916792+00:00
-- url     : https://prove2.me/submissions/fcfcf1d7-bdd7-4549-a8fb-cc1aff75a3a2

-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Source mathematics: Xi Li, Xin (Shane) Wang and Barrie R. Nault.
-- Platform statements and definitions: mikedeng1; statement review: Shuze Chen.
-- Mathematical and measure-theoretic foundations: Mathlib contributors.
import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory Set PPDifferentiation.Costless
namespace PricingResearch
lemma increasing_share (a b q : ℝ) (ha : 0<a) :
    (volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal =
      if (q+b)/a < 0 then 1 else max (1-(q+b)/a) 0 := by
  have h : ∀ x : ℝ, q<a*x-b ↔ (q+b)/a<x := by
    intro x
    rw [div_lt_iff₀ ha]
    constructor <;> intro hx <;> nlinarith
  simp_rw [h]
  split_ifs with hc
  · have hs : {x : ℝ | (q+b)/a<x} ∩ Icc 0 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff,mem_setOf_eq,mem_Icc]
      constructor
      · exact And.right
      · intro hx; exact ⟨lt_of_lt_of_le hc hx.1,hx⟩
    rw [hs,Real.volume_Icc]
    norm_num
  · have hs : {x : ℝ | (q+b)/a<x} ∩ Icc 0 1 = Ioc ((q+b)/a) 1 := by
      ext x
      simp only [mem_inter_iff,mem_setOf_eq,mem_Icc,mem_Ioc]
      constructor
      · intro hx; exact ⟨hx.1,hx.2.2⟩
      · intro hx; exact ⟨hx.1,le_trans (le_of_not_gt hc) hx.1.le,hx.2⟩
    rw [hs,Real.volume_Ioc,ENNReal.toReal_ofReal']
lemma integral_left (a c : ℝ) (ha : 0≤a) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ x in (0:ℝ)..1, max 0 (a*(c-x))) = a*c^2/2 := by
  have hint : IntervalIntegrable (fun x : ℝ => max 0 (a*(c-x))) volume 0 1 :=
    (continuous_const.max (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hleft : (∫ x in (0:ℝ)..c, max 0 (a*(c-x))) = a*c^2/2 := by
    calc
      _ = ∫ x in (0:ℝ)..c, a*(c-x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hc0] at hx
        exact max_eq_right (mul_nonneg ha (sub_nonneg.mpr hx.2))
      _ = a*c^2/2 := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub]
        · simp [integral_id]; ring
        · exact intervalIntegrable_const
        · exact continuous_id.intervalIntegrable _ _
  have hright : (∫ x in c..(1:ℝ), max 0 (a*(c-x))) = 0 := by
    calc
      _ = ∫ _x in c..(1:ℝ), (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hc1] at hx
        exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos ha (sub_nonpos.mpr hx.1))
      _ = 0 := by simp
  have hc : Continuous (fun x : ℝ => max 0 (a*(c-x))) :=
    continuous_const.max (continuous_const.mul (continuous_const.sub continuous_id))
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 c) (hc.intervalIntegrable (μ := volume) c 1)
  rw [hleft,hright,add_zero] at hsum
  exact hsum.symm
lemma asym_share (t q : ℝ) (ht : 0<t) :
    leadShare t (1/2) (-1/2) q = if q<0 then 1 else max (1-q/(2*t)) 0 := by
  have he : ∀ x : ℝ, adv t (1/2) (-1/2) x = (2*t)*x-0 := by intro x; unfold adv; ring
  unfold leadShare
  simp_rw [he]
  rw [increasing_share (2*t) 0 q (by positivity)]
  have hn : q/(2*t)<0 ↔ q<0 := by rw [div_lt_iff₀ (show (0:ℝ)<2*t by positivity)]; simp
  simp only [add_zero,hn]
lemma asym_opt (t : ℝ) (ht : 0<t) :
    IsLeaderOpt t (1/2) (-1/2) t ∧
    (∀ q, IsLeaderOpt t (1/2) (-1/2) q → q=t) ∧
    leadProf t (1/2) (-1/2) t = t/2 := by
  have htne : t≠0 := ne_of_gt ht
  have hv : leadProf t (1/2) (-1/2) t = t/2 := by
    rw [leadProf,asym_share t t ht]
    rw [if_neg (not_lt.mpr ht.le)]
    have he : t/(2*t) = (1:ℝ)/2 := by field_simp <;> ring
    rw [he]
    norm_num
    ring
  have hb : ∀ q, leadProf t (1/2) (-1/2) q ≤ t/2 ∧
      (leadProf t (1/2) (-1/2) q = t/2 → q=t) := by
    intro q
    rw [leadProf,asym_share t q ht]
    split_ifs with hq
    · simp only [mul_one]
      constructor
      · linarith
      · intro h; linarith
    · by_cases hh : q≤2*t
      · rw [max_eq_left (by apply sub_nonneg.mpr; exact (div_le_one (by positivity)).mpr hh)]
        have hi : q*(1-q/(2*t)) = t/2-(q-t)^2/(2*t) := by field_simp <;> ring
        rw [hi]
        have hn : 0≤(q-t)^2/(2*t) := by positivity
        constructor
        · linarith
        · intro he
          have hz : (q-t)^2=0 := (div_eq_zero_iff).mp (by linarith) |>.resolve_right (by positivity)
          nlinarith [sq_nonneg (q-t)]
      · rw [max_eq_right (by apply sub_nonpos.mpr; exact (one_le_div (by positivity)).mpr (le_of_not_ge hh))]
        simp only [mul_zero]
        constructor
        · positivity
        · intro he; linarith
  refine ⟨?_,?_,hv⟩
  · intro q; rw [hv]; exact (hb q).1
  · intro q hq
    apply (hb q).2
    exact le_antisymm (hb q).1 (by have hh := hq t; rw [hv] at hh; exact hh)
lemma asym_follow (t : ℝ) (ht : 0<t) : followProf t (1/2) (-1/2) t = t/4 := by
  have he : ∀ x : ℝ, t-adv t (1/2) (-1/2) x = (2*t)*(1/2-x) := by intro x; unfold adv; ring
  unfold followProf
  simp_rw [he]
  rw [integral_left (2*t) (1/2) (by positivity) (by norm_num) (by norm_num)]
  ring
end PricingResearch
namespace PricingResearch
lemma linear_opt (a b : ℝ) (ha : 0<a) (hb0 : -a<b) (hb1 : b<a) :
    let f := fun q : ℝ => q * (volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal
    (∀ q, f q ≤ (a-b)^2/(4*a)) ∧
    f ((a-b)/2) = (a-b)^2/(4*a) ∧
    (∀ q, f q = (a-b)^2/(4*a) → q=(a-b)/2) := by
  dsimp
  have ha0 : a≠0 := ne_of_gt ha
  have hp : 0<(a-b)^2/(4*a) := div_pos (sq_pos_of_pos (by linarith)) (by positivity)
  have hall : ∀ q, q*(volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal ≤ (a-b)^2/(4*a) ∧
      (q*(volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal = (a-b)^2/(4*a) → q=(a-b)/2) := by
    intro q
    rw [increasing_share a b q ha]
    split_ifs with hq
    · have hq' : q+b<0 := by simpa using (div_lt_iff₀ ha).mp hq
      have hpos : 0<(a+b)^2/(4*a) := div_pos (sq_pos_of_pos (by linarith)) (by positivity)
      have he : (a-b)^2/(4*a)+b=(a+b)^2/(4*a) := by field_simp; ring
      simp only [mul_one]
      constructor
      · linarith
      · intro h; linarith
    · by_cases hh : (q+b)/a≤1
      · rw [max_eq_left (sub_nonneg.mpr hh)]
        have he : q*(1-(q+b)/a) = (a-b)^2/(4*a)-(q-(a-b)/2)^2/a := by field_simp; ring
        rw [he]
        have hn : 0≤(q-(a-b)/2)^2/a := div_nonneg (sq_nonneg _) ha.le
        constructor
        · linarith
        · intro heq
          have hz : (q-(a-b)/2)^2=0 := (div_eq_zero_iff).mp (by linarith) |>.resolve_right ha0
          nlinarith [sq_nonneg (q-(a-b)/2)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hh)),mul_zero]
        exact ⟨hp.le,fun h => (ne_of_gt hp h.symm).elim⟩
  refine ⟨fun q => (hall q).1,?_,fun q => (hall q).2⟩
  rw [increasing_share a b ((a-b)/2) ha,if_neg]
  · rw [max_eq_left]
    · field_simp; ring
    · apply sub_nonneg.mpr
      apply (div_le_one ha).mpr
      linarith
  · apply not_lt.mpr
    apply div_nonneg _ ha.le
    linarith
lemma general_asym (t xA xB : ℝ) (ht : 0<t) (ho : xA<xB)
    (hl : -2<xA+xB) (hh : xA+xB<2) :
    let p := t*(2-xA-xB)*(xB-xA)/2
    IsLeaderOpt t xB xA p ∧ (∀ q,IsLeaderOpt t xB xA q → q=p) ∧
    followProf t xB xA p = t*(xB-xA)*(2+xA+xB)^2/16 ∧
    leadProf t xB xA p = t*(xB-xA)*(2-xA-xB)^2/8 := by
  let a := 2*t*(xB-xA)
  let b := t*(xB-xA)*(xA+xB)
  have hd : 0<t*(xB-xA) := mul_pos ht (sub_pos.mpr ho)
  have ha : 0<a := by dsimp [a]; positivity
  have ha0 : a≠0 := ne_of_gt ha
  have hb0 : -a<b := by dsimp [a,b]; nlinarith [mul_pos hd (show 0<2+xA+xB by linarith)]
  have hb1 : b<a := by dsimp [a,b]; nlinarith [mul_pos hd (show 0<2-xA-xB by linarith)]
  have he : ∀ x : ℝ, adv t xB xA x = a*x-b := by intro x; dsimp [adv,a,b]; ring
  have hf : ∀ q, leadProf t xB xA q = q*(volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal := by
    intro q; unfold leadProf leadShare; simp_rw [he]
  have hp : t*(2-xA-xB)*(xB-xA)/2 = (a-b)/2 := by dsimp [a,b]; ring
  dsimp only
  rw [hp]
  have hc := linear_opt a b ha hb0 hb1
  have hv : leadProf t xB xA ((a-b)/2) = (a-b)^2/(4*a) := by rw [hf]; exact hc.2.1
  refine ⟨?_,?_,?_,?_⟩
  · intro q; rw [hv,hf]; exact hc.1 q
  · intro q hq
    apply hc.2.2 q
    apply le_antisymm (hc.1 q)
    have h := hq ((a-b)/2)
    rw [hv,hf] at h
    exact h
  · have hc0 : 0≤(a+b)/(2*a) := div_nonneg (by linarith) (by positivity)
    have hc1 : (a+b)/(2*a)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    have hr : ∀ x : ℝ, (a-b)/2-adv t xB xA x = a*((a+b)/(2*a)-x) := by
      intro x; rw [he]; field_simp; ring
    unfold followProf
    simp_rw [hr]
    rw [integral_left a ((a+b)/(2*a)) ha.le hc0 hc1]
    dsimp [a,b]
    field_simp
    <;> ring
  · rw [hv]
    dsimp [a,b]
    field_simp
    <;> ring
end PricingResearch


theorem solution (t xA xB : ℝ) (ht : 0 < t)
    (hord : xA < xB) (hlo : -2 < xA + xB) (hhi : xA + xB < 2) :
    let p := t * (2 - xA - xB) * (xB - xA) / 2
    PPDifferentiation.Costless.IsLeaderOpt t xB xA p ∧
    (∀ q : ℝ, PPDifferentiation.Costless.IsLeaderOpt t xB xA q → q = p) ∧
    PPDifferentiation.Costless.followProf t xB xA p = t * (xB - xA) * (2 + xA + xB)^2 / 16 ∧
    PPDifferentiation.Costless.leadProf t xB xA p = t * (xB - xA) * (2 - xA - xB)^2 / 8 := by
  exact PricingResearch.general_asym t xA xB ht hord hlo hhi


