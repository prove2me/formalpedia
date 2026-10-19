-- Prove2me | solution 1 for PPDifferentiation.ShortRun.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T07:37:51.692488+00:00
-- url     : https://prove2.me/submissions/09ebbb84-a7e6-40be-9d1a-d881da234e78

-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Mathematics: Xi Li, Xin (Shane) Wang and Barrie R. Nault.
-- Platform definitions and exact all-real-deviation formulation: mikedeng1; review: Shuze Chen.
-- Formal foundations: Mathlib contributors. No mathematical novelty claimed.
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
namespace PricingResearch
lemma volume_reflect (s : Set ℝ) (hs : MeasurableSet s) :
    volume ((fun x : ℝ => 1-x) ⁻¹' s ∩ Icc 0 1) = volume (s ∩ Icc 0 1) := by
  have he : (fun x : ℝ => 1-x) ⁻¹' s ∩ Icc 0 1 = (fun x : ℝ => 1-x) ⁻¹' (s ∩ Icc 0 1) := by
    ext x; simp only [mem_inter_iff,mem_preimage,mem_Icc]; constructor <;> rintro ⟨h,h1,h2⟩ <;> exact ⟨h,by linarith,by linarith⟩
  rw [he]
  exact (volume.measurePreserving_sub_left (1:ℝ)).measure_preimage (hs.inter measurableSet_Icc).nullMeasurableSet
lemma adv_reflect (t i j x : ℝ) : adv t (1-i) (1-j) x = adv t i j (1-x) := by unfold adv; ring
lemma lead_reflect (t i j p : ℝ) : leadProf t (1-i) (1-j) p = leadProf t i j p := by
  unfold leadProf leadShare
  simp_rw [adv_reflect]
  rw [show {x : ℝ | p<adv t i j (1-x)} = (fun x : ℝ => 1-x) ⁻¹' {x : ℝ | p<adv t i j x} from rfl,
    volume_reflect _ (by unfold adv; measurability)]
lemma follow_reflect (t i j p : ℝ) : followProf t (1-i) (1-j) p = followProf t i j p := by
  unfold followProf
  simp_rw [adv_reflect]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => max 0 (p-adv t i j x)) 1]
  norm_num
lemma pp_reflect (t i j : ℝ) : profPP t (1-i) (1-j) = profPP t i j := by
  unfold profPP
  simp_rw [adv_reflect]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => max 0 (adv t i j x)) 1]
  norm_num
lemma uniform_reflect (t i j pi pj : ℝ) : uProf t (1-i) (1-j) pi pj = uProf t i j pi pj := by
  unfold uProf uShare
  simp_rw [adv_reflect]
  rw [show {x : ℝ | pi-pj<adv t i j (1-x)} = (fun x : ℝ => 1-x) ⁻¹' {x : ℝ | pi-pj<adv t i j x} from rfl,
    volume_reflect _ (by unfold adv; measurability)]
  rw [show {x : ℝ | pi-pj=adv t i j (1-x)} = (fun x : ℝ => 1-x) ⁻¹' {x : ℝ | pi-pj=adv t i j x} from rfl,
    volume_reflect _ (by unfold adv; measurability)]
lemma pp_value (t : ℝ) (ht : 0<t) : profPP t (1/4) (3/4)=t/8 := by
  have he : ∀ x : ℝ, adv t (1/4) (3/4) x = t*(1/2-x) := by intro x; unfold adv; ring
  unfold profPP
  simp_rw [he]
  rw [integral_left t (1/2) ht.le (by norm_num) (by norm_num)]
  ring
lemma uniform_value (t : ℝ) (ht : 0<t) : uProf t (-1/4) (5/4) (3*t/2) (3*t/2)=3*t/4 := by
  have he : ∀ x : ℝ, adv t (-1/4) (5/4) x = (3*t)*(1/2-x) := by intro x; unfold adv; ring
  have hs : {x : ℝ | (3*t/2)-(3*t/2)<adv t (-1/4) (5/4) x} ∩ Icc 0 1 = Ico 0 (1/2) := by
    ext x; simp only [mem_inter_iff,mem_setOf_eq,mem_Icc,mem_Ico,he]
    have hp : 0<3*t := by positivity
    constructor
    · rintro ⟨h,h0,h1⟩; exact ⟨h0,by nlinarith⟩
    · rintro ⟨h0,h1⟩; exact ⟨by nlinarith, h0,by linarith⟩
  have hz : {x : ℝ | (3*t/2)-(3*t/2)=adv t (-1/4) (5/4) x} ∩ Icc 0 1 = {1/2} := by
    ext x; simp only [mem_inter_iff,mem_setOf_eq,mem_Icc,mem_singleton_iff,he]
    constructor
    · rintro ⟨h,_,_⟩; nlinarith
    · intro h; subst x; norm_num
  unfold uProf uShare
  rw [hs,hz,Real.volume_Ico]
  norm_num
  ring
lemma table_values (t F : ℝ) (ht : 0<t) (p₀ p₁ : ℝ)
    (h0 : IsLeaderOpt t (1/2) (-1/2) p₀) (h1 : IsLeaderOpt t (1/2) (3/2) p₁) :
    PPDifferentiation.ShortRun.stage1A t F p₀ p₁ .PP .PP = t/8-F ∧
    PPDifferentiation.ShortRun.stage1B t F p₀ p₁ .PP .PP = t/8-F ∧
    PPDifferentiation.ShortRun.stage1A t F p₀ p₁ .PP .U = t/4-F ∧
    PPDifferentiation.ShortRun.stage1B t F p₀ p₁ .PP .U = t/2 ∧
    PPDifferentiation.ShortRun.stage1A t F p₀ p₁ .U .PP = t/2 ∧
    PPDifferentiation.ShortRun.stage1B t F p₀ p₁ .U .PP = t/4-F ∧
    PPDifferentiation.ShortRun.stage1A t F p₀ p₁ .U .U = 3*t/4 ∧
    PPDifferentiation.ShortRun.stage1B t F p₀ p₁ .U .U = 3*t/4 := by
  have hl : ∀ q : ℝ, leadProf t (1/2) (3/2) q=leadProf t (1/2) (-1/2) q := by
    intro q; convert lead_reflect t (1/2) (-1/2) q using 1 <;> norm_num
  have hf : ∀ q : ℝ, followProf t (1/2) (3/2) q=followProf t (1/2) (-1/2) q := by
    intro q; convert follow_reflect t (1/2) (-1/2) q using 1 <;> norm_num
  have hpp : profPP t (3/4) (1/4)=profPP t (1/4) (3/4) := by
    convert pp_reflect t (1/4) (3/4) using 1 <;> norm_num
  have hu : uProf t (5/4) (-1/4) (3*t/2) (3*t/2)=uProf t (-1/4) (5/4) (3*t/2) (3*t/2) := by
    convert uniform_reflect t (-1/4) (5/4) (3*t/2) (3*t/2) using 1 <;> norm_num
  have h1' : IsLeaderOpt t (1/2) (-1/2) p₁ := by intro q; simpa only [hl] using h1 q
  have hp0 := (asym_opt t ht).2.1 p₀ h0
  have hp1 := (asym_opt t ht).2.1 p₁ h1'
  subst p₀;subst p₁
  simp only [PPDifferentiation.ShortRun.stage1A,PPDifferentiation.ShortRun.stage1B,hl,hf,hpp,hu,
    pp_value t ht,uniform_value t ht,asym_follow t ht,(asym_opt t ht).2.2,and_self]
end PricingResearch
namespace PricingResearch
lemma integral_right (a c : ℝ) (ha : 0≤a) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ x in (0:ℝ)..1, max 0 (a*(x-c))) = a*(1-c)^2/2 := by
  have he : (fun x : ℝ => max 0 (a*(x-c))) = (fun x : ℝ => max 0 (a*((1-c)-(1-x)))) := by
    funext x; congr 1; ring
  rw [he,intervalIntegral.integral_comp_sub_left (fun x : ℝ => max 0 (a*((1-c)-x))) 1]
  norm_num only [sub_self,sub_zero]
  exact integral_left a (1-c) ha (by linarith) (by linarith)
lemma pp_bound (t z : ℝ) (ht : 0<t) : profPP t z (3/4) ≤ t/8 := by
  by_cases hz : z≤3/4
  · have he : ∀ x : ℝ, adv t z (3/4) x = (2*t*(3/4-z))*((z+3/4)/2-x) := by intro x; unfold adv; ring
    by_cases hz0 : z≤ -3/4
    · have hzero : profPP t z (3/4)=0 := by
        unfold profPP
        calc
          _ = ∫ _x in (0:ℝ)..1, (0:ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (show (0:ℝ)≤1 by norm_num)] at hx
            change max 0 (adv t z (3/4) x) = 0
            rw [he]
            apply max_eq_left
            exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hx.1])
          _ = 0 := by simp
      rw [hzero]; positivity
    · unfold profPP
      simp_rw [he]
      rw [integral_left (2*t*(3/4-z)) ((z+3/4)/2) (by positivity) (by linarith) (by linarith)]
      have hn : 0≤t*(z-1/4)^2*(z+5/4) := mul_nonneg (mul_nonneg ht.le (sq_nonneg _)) (by linarith)
      nlinarith
  · have hz' : 0≤z-3/4 := by linarith
    have he : ∀ x : ℝ, adv t z (3/4) x = (2*t*(z-3/4))*(x-(z+3/4)/2) := by intro x; unfold adv; ring
    by_cases hz1 : 5/4≤z
    · have hzero : profPP t z (3/4)=0 := by
        unfold profPP
        calc
          _ = ∫ _x in (0:ℝ)..1, (0:ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (show (0:ℝ)≤1 by norm_num)] at hx
            change max 0 (adv t z (3/4) x) = 0
            rw [he]
            apply max_eq_left
            exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hx.2])
          _ = 0 := by simp
      rw [hzero]; positivity
    · unfold profPP
      simp_rw [he]
      rw [integral_right (2*t*(z-3/4)) ((z+3/4)/2) (by positivity) (by linarith) (by linarith)]
      have hsmall : (1-(z+3/4)/2)^2≤1/16 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsmall (mul_nonneg ht.le hz')
      nlinarith [mul_nonneg ht.le (show 0≤5/4-z by linarith)]
lemma pp_equilibrium (t : ℝ) (ht : 0<t) : IsPosEqPP t (1/4) (3/4) ∧
    profPP t (1/4) (3/4)=t/8 ∧ profPP t (3/4) (1/4)=t/8 := by
  have he : profPP t (3/4) (1/4)=profPP t (1/4) (3/4) := by
    convert pp_reflect t (1/4) (3/4) using 1 <;> norm_num
  refine ⟨⟨?_,?_⟩,pp_value t ht,by rw [he,pp_value t ht]⟩
  · intro x; rw [pp_value t ht]; exact pp_bound t x ht
  · intro x
    rw [he,pp_value t ht]
    have hx : profPP t x (1/4)=profPP t (1-x) (3/4) := by
      convert pp_reflect t (1-x) (3/4) using 1 <;> ring
    rw [hx]; exact pp_bound t (1-x) ht
end PricingResearch
namespace PricingResearch
lemma nonpos_opt (t i j : ℝ) (h : ∀ x ∈ Icc (0:ℝ) 1, adv t i j x ≤ 0) :
    IsLeaderOpt t i j 0 ∧ leadProf t i j 0 = 0 := by
  have hz : leadProf t i j 0=0 := by simp [leadProf]
  refine ⟨?_,hz⟩
  intro q
  rw [hz]
  by_cases hq : q≤0
  · exact mul_nonpos_of_nonpos_of_nonneg hq ENNReal.toReal_nonneg
  · have hs : {x : ℝ | q<adv t i j x} ∩ Icc 0 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx,hx'⟩
      change q<adv t i j x at hx
      linarith [h x hx']
    simp [leadProf,leadShare,hs]
lemma opt_reflect (t i j p : ℝ) : IsLeaderOpt t (1-i) (1-j) p ↔ IsLeaderOpt t i j p := by
  unfold IsLeaderOpt
  simp_rw [lead_reflect]
lemma boundary_opt (a b : ℝ) (ha : 0<a) (hb : b≤-a) :
    (∀ q, q*(volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal ≤ -b) ∧
    (-b)*(volume ({x : ℝ | -b<a*x-b} ∩ Icc 0 1)).toReal = -b := by
  constructor
  · intro q
    rw [increasing_share a b q ha]
    split_ifs with hq
    · have hh := (div_lt_iff₀ ha).mp hq; simp only [zero_mul] at hh;simpa using (show q≤-b by linarith)
    · by_cases hh : (q+b)/a≤1
      · rw [max_eq_left (sub_nonneg.mpr hh)]
        have hqb : 0≤q+b := by
          have hh := mul_nonneg (not_lt.mp hq) ha.le
          rwa [div_mul_cancel₀ _ (ne_of_gt ha)] at hh
        have hn : 0≤(q+b)*(q-a) := mul_nonneg hqb (by linarith)
        calc
          _ = q*(a-q-b)/a := by field_simp;ring
          _ ≤ (-b*a)/a := (div_le_div_iff_of_pos_right ha).mpr (by nlinarith)
          _ = -b := by field_simp
      · rw [max_eq_right (by linarith),mul_zero]; linarith
  · rw [increasing_share a b (-b) ha]
    simp
lemma left_follower (t z : ℝ) (ht : 0<t) (hz : z<1/2) :
    ∃ p, IsLeaderOpt t (1/2) z p ∧ followProf t (1/2) z p ≤ t/4 := by
  by_cases hl : -5/2<z
  · have h := general_asym t z (1/2) ht hz (by linarith) (by linarith)
    refine ⟨_,h.1,?_⟩
    rw [h.2.2.1]
    have he : t/4-t*(1/2-z)*(2+z+1/2)^2/16 = t*(z+1/2)^2*(z+7/2)/16 := by ring
    have hn : 0≤t*(z+1/2)^2*(z+7/2)/16 := div_nonneg (mul_nonneg (mul_nonneg ht.le (sq_nonneg _)) (by linarith)) (by norm_num)
    linarith
  · let a := 2*t*(1/2-z)
    let b := t*(1/2-z)*(z+1/2)
    have ha : 0<a := by dsimp [a]; positivity
    have hb : b≤-a := by
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0≤t*(1/2-z) by positivity) (show z+5/2≤0 by linarith)
      dsimp [a,b];nlinarith
    have he : ∀ x : ℝ, adv t (1/2) z x = a*x-b := by intro x; dsimp [a,b,adv]; ring
    have hf : ∀ q, leadProf t (1/2) z q = q*(volume ({x : ℝ | q<a*x-b} ∩ Icc 0 1)).toReal := by
      intro q;unfold leadProf leadShare;simp_rw [he]
    have h := boundary_opt a b ha hb
    refine ⟨-b,?_,?_⟩
    · intro q;rw [hf,hf,h.2];exact h.1 q
    · have hi : followProf t (1/2) z (-b)=0 := by
        unfold followProf
        calc
          _ = ∫ x in (0:ℝ)..1, (0:ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (by norm_num)] at hx
            dsimp only
            rw [he,max_eq_left]
            nlinarith [mul_nonneg ha.le hx.1]
          _ = 0 := by simp
      rw [hi];positivity
lemma follower_global (t z : ℝ) (ht : 0<t) :
    ∃ p, IsLeaderOpt t (1/2) z p ∧ followProf t (1/2) z p ≤ t/4 := by
  rcases lt_trichotomy z (1/2) with h|h|h
  · exact left_follower t z ht h
  · subst z
    have ha : ∀ x, adv t (1/2) (1/2) x=0 := by intro x;unfold adv;ring
    refine ⟨0,(nonpos_opt t (1/2) (1/2) (fun x _ => (ha x).le)).1,?_⟩
    simp only [followProf,ha,sub_self,max_self,intervalIntegral.integral_zero]
    positivity
  · obtain ⟨p,hp,hv⟩ := left_follower t (1-z) ht (by linarith)
    refine ⟨p,?_,?_⟩
    · have hr := (opt_reflect t (1/2) (1-z) p).mpr hp
      convert hr using 1 <;> ring
    · have hr := follow_reflect t (1/2) (1-z) p
      have h1 : 1-(1/2:ℝ)=1/2 := by norm_num
      rw [h1,sub_sub_cancel] at hr
      linarith
lemma leader_global (t z : ℝ) (ht : 0<t) :
    ∃ p, IsLeaderOpt t z (-1/2) p ∧ leadProf t z (-1/2) p ≤ t/2 := by
  by_cases hl : -1/2<z
  · by_cases hh : z<5/2
    · have h := general_asym t (-1/2) z ht hl (by linarith) (by linarith)
      refine ⟨_,h.1,?_⟩
      rw [h.2.2.2]
      have he : t/2-t*(z- -1/2)*(2- -1/2-z)^2/8 = t*(z-1/2)^2*(7/2-z)/8 := by ring
      have hn : 0≤t*(z-1/2)^2*(7/2-z)/8 := div_nonneg (mul_nonneg (mul_nonneg ht.le (sq_nonneg _)) (by linarith)) (by norm_num)
      linarith
    · have ha : ∀ x ∈ Icc (0:ℝ) 1, adv t z (-1/2) x≤0 := by
        intro x hx
        have h1 : 0≤z+1/2 := by linarith
        have h2 : 2*x-z+1/2≤0 := by linarith [hx.2]
        have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht.le h1) h2
        unfold adv;nlinarith
      exact ⟨0,(nonpos_opt t z (-1/2) ha).1,by rw [(nonpos_opt t z (-1/2) ha).2];positivity⟩
  · have ha : ∀ x ∈ Icc (0:ℝ) 1, adv t z (-1/2) x≤0 := by
      intro x hx
      have h1 : z+1/2≤0 := by linarith
      have h2 : 0≤2*x-z+1/2 := by linarith [hx.1]
      have hn := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ht.le h1) h2
      unfold adv;nlinarith
    exact ⟨0,(nonpos_opt t z (-1/2) ha).1,by rw [(nonpos_opt t z (-1/2) ha).2];positivity⟩
lemma asymmetric_positions (t : ℝ) (ht : 0<t) : PPDifferentiation.ShortRun.IsPosEqAS t (-1/2) (1/2) := by
  have ho := asym_opt t ht
  refine ⟨⟨t,ho.1⟩,?_,?_⟩
  · intro p z hp
    have he := ho.2.1 p hp
    subst p
    rw [asym_follow t ht]
    exact follower_global t z ht
  · intro p z hp
    have he := ho.2.1 p hp
    subst p
    rw [ho.2.2]
    exact leader_global t z ht
end PricingResearch
namespace PricingResearch
lemma u_linear (t i j a b p q : ℝ) (ha : 0<a)
    (he : ∀ x, adv t i j x=a*x-b) :
    uProf t i j p q = p*(volume ({x : ℝ | p<a*x-(b-q)} ∩ Icc 0 1)).toReal := by
  have hs : {x : ℝ | p-q=adv t i j x} ⊆ {(p-q+b)/a} := by
    intro x hx
    simp only [mem_setOf_eq,he] at hx
    simp only [mem_singleton_iff]
    apply (eq_div_iff (ne_of_gt ha)).mpr
    nlinarith
  have hz : volume ({x : ℝ | p-q=adv t i j x} ∩ Icc 0 1)=0 :=
    measure_mono_null ((inter_subset_left).trans hs) (measure_singleton _)
  have hs' : {x : ℝ | p-q<adv t i j x} = {x : ℝ | p<a*x-(b-q)} := by
    ext x;simp only [mem_setOf_eq,he];constructor <;> intro h <;> linarith
  simp [uProf,uShare,hz,hs']
lemma u_best (t i j a b q : ℝ) (ha : 0<a) (hl : -a<b-q) (hh : b-q<a)
    (he : ∀ x,adv t i j x=a*x-b) :
    (∀ p,uProf t i j p q ≤ uProf t i j ((a-b+q)/2) q) ∧
    uProf t i j ((a-b+q)/2) q = (a-b+q)^2/(4*a) := by
  have h := linear_opt a (b-q) ha hl hh
  dsimp only at h
  have hp : (a-b+q)/2 = (a-(b-q))/2 := by ring
  have hv : uProf t i j ((a-b+q)/2) q = (a-b+q)^2/(4*a) := by
    rw [u_linear t i j a b _ q ha he,hp,h.2.1];congr 2;ring
  refine ⟨?_,hv⟩
  intro p
  rw [hv,u_linear t i j a b p q ha he]
  convert h.1 p using 1 <;> ring
lemma uniform_prices_strict (t i j : ℝ) (ht : 0<t) (hij : i<j)
    (hl : (-2 : ℝ) < i + j) (hh : i + j < 4) :
    let p := t*(j-i)*(2+i+j)/3
    let q := t*(j-i)*(4-i-j)/3
    IsPriceNE t i j p q ∧ uProf t i j p q=t*(j-i)*(2+i+j)^2/18 ∧
      uProf t j i q p=t*(j-i)*(4-i-j)^2/18 := by
  let d := t*(j-i)
  let a := 2*d
  let b := d*(i+j)
  let p := d*(2+i+j)/3
  let q := d*(4-i-j)/3
  have hd : 0<d := mul_pos ht (sub_pos.mpr hij)
  have ha : 0<a := by dsimp [a];positivity
  have hsum : -a<b ∧ b<2*a := by
    dsimp [a,b]
    constructor
    · nlinarith [mul_pos hd (show 0<2+i+j by linarith)]
    · nlinarith [mul_pos hd (show 0<4-i-j by linarith)]
  have hep : p=(a+b)/3 := by dsimp [p,a,b];ring
  have heq : q=(2*a-b)/3 := by dsimp [q,a,b];ring
  have hr := u_best t j i a b p ha (by rw [hep];linarith [hsum.1]) (by rw [hep];linarith [hsum.2])
    (fun x => by dsimp [adv,a,b,d];ring)
  have hleft := u_best t (1-i) (1-j) a (a-b) q ha
    (by rw [heq];linarith [hsum.2]) (by rw [heq];linarith [hsum.1])
    (fun x => by dsimp [adv,a,b,d];ring)
  have hpform : (a-(a-b)+q)/2=p := by rw [hep,heq];ring
  have hqform : (a-b+p)/2=q := by rw [hep,heq];ring
  rw [hpform] at hleft
  rw [hqform] at hr
  simp_rw [uniform_reflect] at hleft
  change IsPriceNE t i j p q ∧ uProf t i j p q=_ ∧ uProf t j i q p=_
  refine ⟨⟨hleft.1,hr.1⟩,?_,?_⟩
  · rw [hleft.2]
    dsimp [a,b,q,d]
    field_simp
    <;> ring
  · rw [hr.2]
    dsimp [a,b,p,d]
    field_simp
    <;> ring
lemma coincident_price (t i : ℝ) : IsPriceNE t i i 0 0 ∧ uProf t i i 0 0=0 := by
  have hz : uProf t i i 0 0=0 := by simp [uProf]
  have hb : ∀ p,uProf t i i p 0≤0 := by
    intro p
    by_cases hp : p≤0
    · apply mul_nonpos_of_nonpos_of_nonneg hp
      unfold uShare
      positivity
    · have ha : ∀ x, adv t i i x=0 := by intro x;unfold adv;ring
      simp only [uProf,uShare,ha,sub_zero]
      have h1 : {x : ℝ | p<0}=∅ := by ext x;simp [not_lt.mpr (not_le.mp hp).le]
      have h2 : {x : ℝ | p=0}=∅ := by ext x;simp [ne_of_gt (not_le.mp hp)]
      simp [h1,h2]
  exact ⟨⟨by simpa [hz] using hb,by simpa [hz] using hb⟩,hz⟩
lemma uniform_prices (t i j : ℝ) (ht : 0<t) (hij : i≤j)
    (hl : (-2 : ℝ) < i + j) (hh : i + j < 4) :
    let p := t*(j-i)*(2+i+j)/3
    let q := t*(j-i)*(4-i-j)/3
    IsPriceNE t i j p q ∧ uProf t i j p q=t*(j-i)*(2+i+j)^2/18 ∧
      uProf t j i q p=t*(j-i)*(4-i-j)^2/18 := by
  rcases hij.eq_or_lt with h|h
  · subst j
    simp only [sub_self,mul_zero,zero_mul,zero_div]
    exact ⟨(coincident_price t i).1,(coincident_price t i).2,(coincident_price t i).2⟩
  · exact uniform_prices_strict t i j ht h hl hh
end PricingResearch
namespace PricingResearch
noncomputable def pricePay (a b p q : ℝ) : ℝ := p * max (min (1-(p+b-q)/a) 1) 0
lemma pricePay_formula (t i j a b p q : ℝ) (ha : 0<a)
    (he : ∀ x,adv t i j x=a*x-b) : uProf t i j p q=pricePay a b p q := by
  rw [u_linear t i j a b p q ha he,increasing_share a (b-q) p ha]
  have heq : p+(b-q)=p+b-q := by ring
  rw [heq]
  unfold pricePay
  by_cases h : (p+b-q)/a<0
  · rw [if_pos h,min_eq_right (by linarith),max_eq_left (by norm_num)]
  · rw [if_neg h,min_eq_left (by linarith)]
lemma pricePay_zero (a b p q : ℝ) (ha : 0<a) (h : a≤p+b-q) : pricePay a b p q=0 := by
  have hr : 1≤(p+b-q)/a := (le_div_iff₀ ha).mpr (by simpa using h)
  simp [pricePay,max_eq_right (show min (1-(p+b-q)/a) 1≤0 from (min_le_left _ _).trans (by linarith))]
lemma pricePay_full (a b p q : ℝ) (ha : 0<a) (h : p+b-q≤0) : pricePay a b p q=p := by
  have hr : (p+b-q)/a≤0 := div_nonpos_of_nonpos_of_nonneg h ha.le
  simp [pricePay,min_eq_right (show 1≤1-(p+b-q)/a by linarith)]
lemma pricePay_pos (a b p q : ℝ) (ha : 0<a) (hp : 0<p) (hm : p<a-b+q) : 0<pricePay a b p q := by
  have hr : (p+b-q)/a<1 := (div_lt_one ha).mpr (by linarith)
  unfold pricePay
  exact mul_pos hp (lt_max_of_lt_left (lt_min (by linarith) (by norm_num)))
lemma zero_best (a b q : ℝ) (ha : 0<a) (h : ∀ p, pricePay a b p q≤0) : a-b+q≤0 := by
  by_contra hm
  have hp := pricePay_pos a b ((a-b+q)/2) q ha (by linarith) (by linarith)
  linarith [h ((a-b+q)/2)]
lemma price_foc (a b p q : ℝ) (ha : 0<a) (h0 : 0<p+b-q) (h1 : p+b-q<a)
    (hbest : ∀ z,pricePay a b z q≤pricePay a b p q) : 2*p=a-b+q := by
  have he : (fun z => pricePay a b z q) =ᶠ[nhds p] (fun z => z*(1-(z+b-q)/a)) := by
    filter_upwards [Ioo_mem_nhds (show q-b<p by linarith) (show p<q-b+a by linarith)] with z hz
    have hr0 : 0≤(z+b-q)/a := div_nonneg (by linarith [hz.1]) ha.le
    have hr1 : (z+b-q)/a≤1 := (div_le_one ha).mpr (by linarith [hz.2])
    simp only [pricePay,min_eq_left (show 1-(z+b-q)/a≤1 by linarith),max_eq_left (show 0≤1-(z+b-q)/a by linarith)]
  have hd : HasDerivAt (fun z : ℝ => z*(1-(z+b-q)/a)) (1-(p+b-q)/a-p/a) p := by
    convert (hasDerivAt_id p).mul ((hasDerivAt_const p (1:ℝ)).sub (((hasDerivAt_id p).add_const b |>.sub_const q).div_const a)) using 1 <;> first | rfl | (dsimp only [Pi.sub_apply,id_eq]; ring)
  have hm : IsLocalMax (fun z => pricePay a b z q) p := Filter.Eventually.of_forall hbest
  have hz := hm.hasDerivAt_eq_zero (hd.congr_of_eventuallyEq he)
  field_simp at hz
  linarith
lemma price_classification (a b p q : ℝ) (ha : 0<a)
    (hp : ∀ z,pricePay a b z q≤pricePay a b p q)
    (hq : ∀ z,pricePay a (a-b) z p≤pricePay a (a-b) q p) :
    pricePay a b p q=0 ∨ pricePay a b p q≤-b ∨
      (-a<b ∧ b<2*a ∧ pricePay a b p q=(2*a-b)^2/(9*a)) := by
  by_cases h0 : p+b-q≤0
  · have hz : pricePay a (a-b) q p=0 := pricePay_zero _ _ _ _ ha (by linarith)
    have hh := zero_best a (a-b) p ha (fun z => by simpa [hz] using hq z)
    exact Or.inr (Or.inl (by rw [pricePay_full _ _ _ _ ha h0];linarith))
  · by_cases h1 : a≤p+b-q
    · exact Or.inl (pricePay_zero _ _ _ _ ha h1)
    · have h0' : 0<p+b-q := not_le.mp h0
      have h1' : p+b-q<a := not_le.mp h1
      have hp' := price_foc a b p q ha h0' h1' hp
      have hq' := price_foc a (a-b) q p ha (by linarith) (by linarith) hq
      have hpe : p=(2*a-b)/3 := by linarith
      have hqe : q=(a+b)/3 := by linarith
      refine Or.inr (Or.inr ⟨by linarith,by linarith,?_⟩)
      have hr0 : 0≤(p+b-q)/a := div_nonneg h0'.le ha.le
      have hr1 : (p+b-q)/a≤1 := (div_le_one ha).mpr h1'.le
      unfold pricePay
      rw [min_eq_left (by linarith),max_eq_left (by linarith),hpe,hqe]
      field_simp
      <;> ring
end PricingResearch
namespace PricingResearch
lemma coincident_value (t i p q : ℝ) : uProf t i i p q=if p<q then p else if p=q then p/2 else 0 := by
  have ha : ∀ x,adv t i i x=0 := by intro x;unfold adv;ring
  unfold uProf uShare
  simp_rw [ha]
  by_cases h : p<q
  · have hs : {x : ℝ | p-q<0}=univ := by ext;simp [show p-q<0 by linarith]
    have he : {x : ℝ | p-q=0}=∅ := by ext;simp [show p-q≠0 by linarith]
    simp [hs,he,h,Real.volume_Icc]
  · have hs : {x : ℝ | p-q<0}=∅ := by ext;simp [show ¬p-q<0 by linarith]
    rw [hs]
    by_cases he : p=q
    · subst q;simp [Real.volume_Icc];ring
    · have hs' : {x : ℝ | p-q=0}=∅ := by ext;simp [sub_ne_zero.mpr he]
      simp [hs',h,he]
lemma coincident_bound (t i p q : ℝ) (h : IsPriceNE t i i p q) : uProf t i i p q≤0 := by
  by_cases hp : p≤0
  · apply mul_nonpos_of_nonpos_of_nonneg hp
    unfold uShare;positivity
  · by_cases hlt : p<q
    · have hh := h.2 (p/2)
      rw [coincident_value,coincident_value] at hh
      simp only [if_pos (show p/2<p by linarith),if_neg (show ¬q<p by linarith),if_neg (show q≠p by linarith)] at hh
      linarith
    · by_cases he : p=q
      · subst q
        have hh := h.1 (3*p/4)
        rw [coincident_value,coincident_value] at hh
        simp only [if_pos (show 3*p/4<p by linarith),lt_self_iff_false,if_false,if_true] at hh
        linarith
      · simp [coincident_value,hlt,he]
lemma uniform_deviation_bound (t z p q : ℝ) (ht : 0<t)
    (hne : IsPriceNE t z (5/4) p q) : uProf t z (5/4) p q≤3*t/4 := by
  rcases lt_trichotomy z (5/4) with hz|hz|hz
  · let d := t*(5/4-z)
    let a := 2*d
    let b := d*(3/4-z)
    have hd : 0<d := mul_pos ht (by linarith)
    have ha : 0<a := by dsimp [a];positivity
    have hf : ∀ r s,uProf t z (5/4) r s=pricePay a b r s := by
      intro r s
      rw [← uniform_reflect t z (5/4) r s]
      exact pricePay_formula _ _ _ _ _ _ _ ha (fun x => by dsimp [adv,a,b,d];ring)
    have hg : ∀ r s,uProf t (5/4) z r s=pricePay a (a-b) r s := by
      intro r s
      exact pricePay_formula _ _ _ _ _ _ _ ha (fun x => by dsimp [adv,a,b,d];ring)
    have hc := price_classification a b p q ha (fun r => by simpa only [hf] using hne.1 r)
      (fun r => by simpa only [hg] using hne.2 r)
    rw [hf]
    rcases hc with hc|hc|⟨hlo,hhi,hv⟩
    · rw [hc];positivity
    · have he : t/16-(-b)=t*(z-1)^2 := by dsimp [b,d];ring
      have hn : 0≤t*(z-1)^2 := mul_nonneg ht.le (sq_nonneg _)
      linarith
    · have hzlo : -13/4<z := by
        by_contra hh
        have hn := mul_nonpos_of_nonneg_of_nonpos hd.le (show z+13/4≤0 by linarith)
        dsimp [a,b] at hhi
        nlinarith
      have he : (2*a-b)^2/(9*a)=t*(5/4-z)*(13/4+z)^2/18 := by
        dsimp [a,b,d];field_simp <;> ring
      rw [hv,he]
      have hid : 3*t/4-t*(5/4-z)*(13/4+z)^2/18=t*(4*z+1)^2*(4*z+19)/1152 := by ring
      have hn : 0≤t*(4*z+1)^2*(4*z+19)/1152 := div_nonneg (mul_nonneg (mul_nonneg ht.le (sq_nonneg _)) (by linarith)) (by norm_num)
      linarith
  · subst z
    have h := coincident_bound t (5/4) p q hne
    linarith
  · let d := t*(z-5/4)
    let a := 2*d
    let b := d*(z+5/4)
    have hd : 0<d := mul_pos ht (by linarith)
    have ha : 0<a := by dsimp [a];positivity
    have hf : ∀ r s,uProf t z (5/4) r s=pricePay a b r s := by
      intro r s
      exact pricePay_formula _ _ _ _ _ _ _ ha (fun x => by dsimp [adv,a,b,d];ring)
    have hg : ∀ r s,uProf t (5/4) z r s=pricePay a (a-b) r s := by
      intro r s
      rw [← uniform_reflect t (5/4) z r s]
      exact pricePay_formula _ _ _ _ _ _ _ ha (fun x => by dsimp [adv,a,b,d];ring)
    have hc := price_classification a b p q ha (fun r => by simpa only [hf] using hne.1 r)
      (fun r => by simpa only [hg] using hne.2 r)
    rw [hf]
    rcases hc with hc|hc|⟨hlo,hhi,hv⟩
    · rw [hc];positivity
    · have hb : 0≤b := mul_nonneg hd.le (by linarith)
      linarith
    · have hzhi : z<11/4 := by
        by_contra hh
        have hn := mul_nonneg hd.le (show 0≤z-11/4 by linarith)
        dsimp [a,b] at hhi
        nlinarith
      have he : (2*a-b)^2/(9*a)=t*(z-5/4)*(11/4-z)^2/18 := by
        dsimp [a,b,d];field_simp <;> ring
      rw [hv,he]
      have hid : t/36-t*(z-5/4)*(11/4-z)^2/18=t*(13-4*z)*(4*z-7)^2/1152 := by ring
      have hn : 0≤t*(13-4*z)*(4*z-7)^2/1152 := div_nonneg (mul_nonneg (mul_nonneg ht.le (by linarith)) (sq_nonneg _)) (by norm_num)
      linarith
lemma uniform_positions (t : ℝ) (ht : 0<t) : PPDifferentiation.ShortRun.IsPosEqUU t (-1/4) (5/4) (3*t/2) (3*t/2) := by
  have hprice := uniform_prices t (-1/4) (5/4) ht (by norm_num) (by norm_num) (by norm_num)
  have hp : t*(5/4-(-1/4))*(2+(-1/4)+5/4)/3=3*t/2 := by ring
  have hq : t*(5/4-(-1/4))*(4-(-1/4)-5/4)/3=3*t/2 := by ring
  dsimp only at hprice
  rw [hp,hq] at hprice
  refine ⟨hprice.1,?_,?_⟩
  · intro z p q hn
    rw [uniform_value t ht]
    exact uniform_deviation_bound t z p q ht hn
  · intro z p q hn
    have href : IsPriceNE t (1-z) (5/4) q p := by
      constructor
      · intro r
        have h := hn.2 r
        have h1 : (5/4:ℝ)=1-(-1/4) := by norm_num
        rw [h1,uniform_reflect,uniform_reflect]
        exact h
      · intro r
        have h := hn.1 r
        have h1 : (5/4:ℝ)=1-(-1/4) := by norm_num
        rw [h1,uniform_reflect,uniform_reflect]
        exact h
    have hh := uniform_deviation_bound t (1-z) q p ht href
    have h1 : (5/4:ℝ)=1-(-1/4) := by norm_num
    rw [h1,uniform_reflect] at hh
    have hv : uProf t (5/4) (-1/4) (3*t/2) (3*t/2)=3*t/4 := by
      convert uniform_value t ht using 1
      convert uniform_reflect t (-1/4) (5/4) (3*t/2) (3*t/2) using 1 <;> norm_num
    rw [hv]
    exact hh
end PricingResearch
namespace PricingResearch
open PPDifferentiation.ShortRun
lemma as_reflection (t f l : ℝ) (h : IsPosEqAS t f l) : IsPosEqAS t (1-f) (1-l) := by
  rcases h.1 with ⟨p,hp⟩
  refine ⟨⟨p,(opt_reflect t l f p).mpr hp⟩,?_,?_⟩
  · intro p0 z hp0
    obtain ⟨r,hr,hv⟩ := h.2.1 p0 (1-z) ((opt_reflect t l f p0).mp hp0)
    refine ⟨r,?_,?_⟩
    · convert (opt_reflect t l (1-z) r).mpr hr using 1 <;> ring
    · calc
        _ = followProf t l (1-z) r := by convert follow_reflect t l (1-z) r using 1 <;> ring
        _ ≤ followProf t l f p0 := hv
        _ = _ := (follow_reflect t l f p0).symm
  · intro p0 z hp0
    obtain ⟨r,hr,hv⟩ := h.2.2 p0 (1-z) ((opt_reflect t l f p0).mp hp0)
    refine ⟨r,?_,?_⟩
    · convert (opt_reflect t (1-z) f r).mpr hr using 1 <;> ring
    · calc
        _ = leadProf t (1-z) f r := by convert lead_reflect t (1-z) f r using 1 <;> ring
        _ ≤ leadProf t l f p0 := hv
        _ = _ := (lead_reflect t l f p0).symm



theorem main (t F : ℝ) (ht : 0 < t) (hF : 0 ≤ F) :
    IsPosEqUU t (-1/4) (5/4) (3*t/2) (3*t/2) ∧
    PPDifferentiation.Costless.IsPosEqPP t (1/4) (3/4) ∧
    IsPosEqAS t (-1/2) (1/2) ∧
    IsPosEqAS t (3/2) (1/2) ∧
    (∃ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ ∧
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁) ∧
    ∀ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ →
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁ →
      (∀ sB : PPChoice, stage1A t F p₀ p₁ .PP sB < stage1A t F p₀ p₁ .U sB) ∧
      (∀ sA : PPChoice, stage1B t F p₀ p₁ sA .PP < stage1B t F p₀ p₁ sA .U) ∧
      (∀ sA sB : PPChoice, IsPureNE (stage1A t F p₀ p₁) (stage1B t F p₀ p₁) sA sB ↔
        sA = .U ∧ sB = .U) := by
  have hleft := asymmetric_positions t ht
  have hright : IsPosEqAS t (3/2) (1/2) := by
    convert as_reflection t (-1/2) (1/2) hleft using 1 <;> norm_num
  refine ⟨uniform_positions t ht,(pp_equilibrium t ht).1,hleft,hright,?_,?_⟩
  · obtain ⟨p,hp⟩ := hleft.1
    obtain ⟨q,hq⟩ := hright.1
    exact ⟨p,q,hp,hq⟩
  · intro p0 p1 h0 h1
    rcases table_values t F ht p0 p1 h0 h1 with ⟨app,bpp,apu,bpu,aup,bup,auu,buu⟩
    have hA : ∀ b : PPChoice, stage1A t F p0 p1 .PP b < stage1A t F p0 p1 .U b := by
      intro b;cases b
      · rw [app,aup];linarith
      · rw [apu,auu];linarith
    have hB : ∀ a : PPChoice, stage1B t F p0 p1 a .PP < stage1B t F p0 p1 a .U := by
      intro a;cases a
      · rw [bpp,bpu];linarith
      · rw [bup,buu];linarith
    refine ⟨hA,hB,?_⟩
    intro a b
    constructor
    · intro hn
      constructor
      · cases a with
        | PP => exact False.elim ((not_le_of_gt (hA b)) (hn.1 .U))
        | U => rfl
      · cases b with
        | PP => exact False.elim ((not_le_of_gt (hB a)) (hn.2 .U))
        | U => rfl
    · rintro ⟨rfl,rfl⟩
      constructor
      · intro a;cases a
        · exact (hA .U).le
        · rfl
      · intro b;cases b
        · exact (hB .U).le
        · rfl




end PricingResearch
open PPDifferentiation.ShortRun


theorem solution (t F : ℝ) (ht : 0 < t) (hF : 0 ≤ F) :
    IsPosEqUU t (-1/4) (5/4) (3*t/2) (3*t/2) ∧
    PPDifferentiation.Costless.IsPosEqPP t (1/4) (3/4) ∧
    IsPosEqAS t (-1/2) (1/2) ∧
    IsPosEqAS t (3/2) (1/2) ∧
    (∃ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ ∧
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁) ∧
    ∀ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ →
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁ →
      (∀ sB : PPChoice, stage1A t F p₀ p₁ .PP sB < stage1A t F p₀ p₁ .U sB) ∧
      (∀ sA : PPChoice, stage1B t F p₀ p₁ sA .PP < stage1B t F p₀ p₁ sA .U) ∧
      (∀ sA sB : PPChoice, IsPureNE (stage1A t F p₀ p₁) (stage1B t F p₀ p₁) sA sB ↔
        sA = .U ∧ sB = .U) := by
  exact PricingResearch.main t F ht hF


