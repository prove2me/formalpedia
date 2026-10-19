-- Prove2me | solution 1 for PPDifferentiation.ShortRun.both_pp_positions
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:55:31.173462+00:00
-- url     : https://prove2.me/submissions/6ade5c0b-4c22-452a-89bc-2ff5870f581f

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


theorem solution (t : ℝ) (ht : 0 < t) :
    PPDifferentiation.Costless.IsPosEqPP t (1/4) (3/4) ∧
    PPDifferentiation.Costless.profPP t (1/4) (3/4) = t/8 ∧
    PPDifferentiation.Costless.profPP t (3/4) (1/4) = t/8 := by
  exact PricingResearch.pp_equilibrium t ht


