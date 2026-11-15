-- Prove2me | solution 1 for StableVotingDistortion.lemma_14_i
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:20.922125+00:00
-- url     : https://prove2.me/submissions/b194464b-db73-4325-935a-cc3ac76cd982

import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_VerifierHypotheses
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Mathlib

-- Source module PrimitiveBounds
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

theorem primitive_sandwich {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b-a)*ϕ b ≤ J ϕ b - J ϕ a ∧ J ϕ b - J ϕ a ≤ (b-a)*ϕ a := by
  have hi {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : IntervalIntegrable ϕ volume x y :=
    (h.continuousOn.mono (Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  have hdiff : J ϕ b - J ϕ a = ∫ r in a..b, ϕ r := by
    have hs := intervalIntegral.integral_add_adjacent_intervals (hi (le_refl 0) ha (hab.trans hb)) (hi ha hab hb)
    unfold J
    linarith
  rw [hdiff]
  have hlow := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := ϕ b)) (hi ha hab hb)
    (fun r hr => h.antitoneOn ⟨ha.trans hr.1, hr.2.trans hb⟩ ⟨ha.trans hab, hb⟩ hr.2)
  have hhi := intervalIntegral.integral_mono_on hab (hi ha hab hb) (intervalIntegrable_const (c := ϕ a))
    (fun r hr => h.antitoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hr.1, hr.2.trans hb⟩ hr.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using And.intro hlow hhi

theorem eq_43_44 {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ) :
    (∀ p q, 0 ≤ q → q ≤ p → p ≤ 1 →
      deltaP ϕ p q ≤ p - q ∧ deltaP ϕ p q ≤ (1 - p) * ϕ q ∧ q * ϕ q ≤ J ϕ q) ∧
      ∀ p q z, 0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 → KP ϕ p q z ≤ -(p - q) * ϕ z - J ϕ q := by
  have h0 : J ϕ 0 = 0 := by simp [J]
  have h1 : J ϕ 1 = 0 := hϕ.integral_eq_zero
  have hleft (r : ℝ) (hr : r ∈ Icc 0 1) := (primitive_sandwich hϕ (le_refl 0) hr.1 hr.2).1
  have hright (r : ℝ) (hr : r ∈ Icc 0 1) := primitive_sandwich hϕ hr.1 hr.2 (le_refl 1)
  simp only [h0,h1,hϕ.at_one,sub_zero,zero_sub] at hleft hright
  have hJ (r : ℝ) (hr : r ∈ Icc 0 1) : 0 ≤ J ϕ r := by
    by_cases hp : 0 ≤ ϕ r
    · exact (mul_nonneg hr.1 hp).trans (hleft r hr)
    · have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr.2) (le_of_not_ge hp)
      linarith [(hright r hr).2]
  constructor
  · intro p q hq hqp hp
    let r := 1-p+q
    have hr : r ∈ Icc 0 1 := ⟨by dsimp [r]; linarith,by dsimp [r]; linarith⟩
    have hs := primitive_sandwich hϕ hq (show q≤r by dsimp [r]; linarith) hr.2
    have he : r-q=1-p := by dsimp [r]; ring
    rw [he] at hs
    change J ϕ r - J ϕ q ≤ _ ∧ J ϕ r - J ϕ q ≤ _ ∧ _
    refine ⟨?_,hs.2,hleft q ⟨hq,hqp.trans hp⟩⟩
    have hh := (hright r hr).1
    dsimp [r] at hh ⊢
    linarith [hJ q ⟨hq,hqp.trans hp⟩]
  · intro p q z hq hqp hpz hz
    have h := (primitive_sandwich hϕ (show 0≤z-p+q by linarith) (show z-p+q≤z by linarith) hz).1
    have he : z-(z-p+q)=p-q := by ring
    rw [he] at h
    unfold KP
    linarith

end StableVotingDistortion
end

-- Source module ScoreProperties
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

theorem gPhi_properties {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ) :
    ϕ lam = 0 ∧ (∀ r ∈ Set.Icc lam 1, ϕ r ≤ 0) ∧ IsActivation (gPhi ϕ) ∧
      gPhi ϕ 0 = 0 ∧ gPhi ϕ 1 = 1 ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1, ϕ r = (1 + ϕ 0) * ((∫ u in (0 : ℝ)..1, gPhi ϕ u) - gPhi ϕ r) := by
  have hl : lam ∈ Icc 0 1 := ⟨h.lam_mem.1.le,h.lam_mem.2.le⟩
  have h0 : 0 < ϕ 0 := h.pos 0 ⟨le_rfl,h.lam_mem.1⟩
  have hd : 0 < 1+ϕ 0 := by linarith
  have hpt : MapsTo ϕ (Ico 0 lam) (Ici 0) := fun x hx => (h.pos x hx).le
  have hc : ContinuousOn ϕ (closure (Ico 0 lam)) := by
    rw [closure_Ico h.lam_mem.1.ne]
    exact h.continuousOn.mono (Icc_subset_Icc le_rfl hl.2)
  have hclosed := hpt.closure_of_continuousOn hc
  rw [closure_Ico h.lam_mem.1.ne, isClosed_Ici.closure_eq] at hclosed
  have hz : ϕ lam = 0 := le_antisymm (by linarith [h.le_lam_sub lam hl]) (hclosed ⟨hl.1,le_rfl⟩)
  have hm : MonotoneOn (gPhi ϕ) (Icc 0 1) := by
    intro x hx y hy hxy
    apply div_le_div_of_nonneg_right _ hd.le
    linarith [h.antitoneOn hx hy hxy]
  have hz0 : gPhi ϕ 0=0 := by simp [gPhi]
  have hz1 : gPhi ϕ 1=1 := by
    rw [gPhi,h.at_one,sub_neg_eq_add,add_comm (ϕ 0) 1,div_self hd.ne']
  have hi := h.continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ)≤1)
  have hmean : (∫ u in (0:ℝ)..1, gPhi ϕ u) = ϕ 0/(1+ϕ 0) := by
    simp only [gPhi]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (f := fun _ => ϕ 0)
      (g := ϕ) intervalIntegrable_const hi, h.integral_eq_zero, intervalIntegral.integral_const]
    simp
  refine ⟨hz,fun r hr => ?_, ⟨?_,hm,?_⟩,hz0,hz1,fun r _ => ?_⟩
  · rw [← hz]; exact h.antitoneOn hl ⟨hl.1.trans hr.1,hr.2⟩ hr.1
  · exact (continuousOn_const.sub h.continuousOn).div_const _
  · intro z hz
    exact ⟨hz0 ▸ hm (by norm_num) hz hz.1,hz1 ▸ hm hz (by norm_num) hz.2⟩
  · rw [hmean,gPhi]
    field_simp [hd.ne'] <;> ring

end StableVotingDistortion
end

-- Source module SmallMass
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set
theorem lemma_14_i {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p0 : ℝ} (hp0 : 0 < p0) (hp0lam : p0 < lam) {β0 : ℝ} (hβ0 : 0 < β0)
    (h45a : 1 ≤ β0 * ϕ p0) (h45b : p0 * (1 + β0 * (1 + ϕ 0)) ≤ lam)
    (h45c : ∀ x ∈ Set.Icc 0 lam, p0 * (1 - β0 * (ϕ p0 - ϕ x)) ≤ sigma lam ϕ x) :
    ∀ p ∈ Set.Ioc 0 p0,
      Eq37 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p ∧
        Eq38 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p := by
  intro p hp
  let B := β0
  let C := fun x => max ((1+B*p)*ϕ x-(lam-x)) 0
  have H := eq_43_44 hϕ
  have hl := hϕ.lam_mem
  have p1 : p ≤ 1 := hp.2.trans (hp0lam.le.trans hl.2.le)
  have h0 : 0 < ϕ 0 := hϕ.pos 0 ⟨le_rfl,hl.1⟩
  have hB : 0 ≤ B := hβ0.le
  have hF : 0 ≤ 1+B*(1+ϕ 0) := by positivity
  have hlim := (mul_le_mul_of_nonneg_right hp.2 hF).trans h45b
  have atq (q : ℝ) (hq : 0≤q) (hqp : q≤p) : ϕ p0 ≤ ϕ q :=
    hϕ.antitoneOn ⟨hq,hqp.trans p1⟩ ⟨hp0.le,hp0lam.le.trans hl.2.le⟩ (hqp.trans hp.2)
  have jbound (q : ℝ) (hq : 0≤q) (hqp : q≤p) : q-B*J ϕ q ≤ 0 := by
    have hj := (H.1 _ _ hq hqp p1).2.2
    have hqφ : 1 ≤ B*ϕ q := h45a.trans (mul_le_mul_of_nonneg_left (atq q hq hqp) hB)
    nlinarith only [mul_le_mul_of_nonneg_left hj hB,mul_le_mul_of_nonneg_left hqφ hq]
  have cmax (x : ℝ) (hx : x ∈ Ico 0 lam) : C x ≤ B*p*ϕ 0 := by
    have hm := hϕ.antitoneOn (show (0:ℝ)∈Icc 0 1 by norm_num) ⟨hx.1,hx.2.le.trans hl.2.le⟩ hx.1
    apply max_le
    · have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg hB hp.1.le)
      nlinarith only [hh,hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hl.2.le⟩]
    · exact mul_nonneg (mul_nonneg hB hp.1.le) h0.le
  have base (q : ℝ) (hq : 0≤q) (hqp : q≤p) :
      q+B*deltaP ϕ p q+B*p*ϕ 0 ≤ lam := by
    have hh := mul_le_mul_of_nonneg_left (H.1 _ _ hq hqp p1).1 hB
    nlinarith only [hh,hlim,hqp,mul_nonneg hB hq]
  have lowK (q z : ℝ) (hq : 0≤q) (hqp : q≤p) (hpz : p≤z) (hz : z≤1) (hzp : 0≤ϕ z) :
      q+B*KP ϕ p q z ≤ 0 := by
    have hk := mul_le_mul_of_nonneg_left (H.2 p q z hq hqp hpz hz) hB
    have hn := mul_nonneg hB (mul_nonneg (sub_nonneg.mpr hqp) hzp)
    nlinarith only [hk,hn,jbound q hq hqp]
  constructor
  · intro x hx
    change (∀ q, 0≤q → q ≤ min p x → q+B*deltaP ϕ p q+C x ≤ lam) ∧ _
    constructor
    · intro q hq hqp
      linarith [base q hq (hqp.trans (min_le_left _ _)),cmax x hx]
    · intro q hq hqp hpx
      change q+B*KP ϕ p q x+C x ≤ 0
      dsimp only [C]
      rw [add_max]
      apply max_le
      · have hk := mul_le_mul_of_nonneg_left (H.2 p q x hq hqp hpx (hx.2.le.trans hl.2.le)) hB
        have hj := mul_le_mul_of_nonneg_left (H.1 _ _ hq hqp p1).2.2 hB
        have hsig : 0 ≤ sigma lam ϕ x := sub_nonneg.mpr (hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hl.2.le⟩)
        have hneeded : q*(1-B*(ϕ q-ϕ x)) ≤ sigma lam ϕ x := by
          have hco : 1-B*(ϕ q-ϕ x) ≤ 1-B*(ϕ p0-ϕ x) := by
            linarith [mul_le_mul_of_nonneg_left (sub_le_sub_right (atq q hq hqp) (ϕ x)) hB]
          by_cases hc : 0 ≤ 1-B*(ϕ p0-ϕ x)
          · exact (mul_le_mul_of_nonneg_left hco hq).trans
              ((mul_le_mul_of_nonneg_right (hqp.trans hp.2) hc).trans (h45c x ⟨hx.1,hx.2.le⟩))
          · exact (mul_nonpos_of_nonneg_of_nonpos hq (hco.trans (le_of_not_ge hc))).trans hsig
        unfold sigma at hneeded
        nlinarith only [hk,hj,hneeded]
      · simpa using lowK q x hq hqp hpx (hx.2.le.trans hl.2.le) (hϕ.pos x hx).le
  · intro x hx
    have hxφ := hϕ.pos x hx
    have hzero (q : ℝ) (hq : q≤p) : Wx lam ϕ x q=0 := if_pos (hq.trans (hp.2.trans hp0lam.le))
    constructor
    · intro q hq hqp
      have hb := base q hq hqp
      have hsmall : q+B*deltaP ϕ p q ≤ lam := by nlinarith only [hb,mul_nonneg (mul_nonneg hB hp.1.le) h0.le]
      change ϕ x*(q+B*deltaP ϕ p q+Wx lam ϕ x q-lam) ≤ max (-ϕ q) 0*C x
      rw [hzero q hqp,add_zero]
      exact (mul_nonpos_of_nonneg_of_nonpos hxφ.le (sub_nonpos.mpr hsmall)).trans
        (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · intro q z hq hqp hpz hz
      change ϕ x*(q+B*KP ϕ p q z+Wx lam ϕ x q-Wx lam ϕ x z) ≤ max (-ϕ z) 0*C x
      rw [hzero q hqp,add_zero]
      by_cases hzL : z≤lam
      · have hpos : 0≤ϕ z := by
          have hh := hϕ.antitoneOn ⟨hp.1.le.trans hpz,hz⟩ ⟨hl.1.le,hl.2.le⟩ hzL
          rwa [(gPhi_properties hϕ).1] at hh
        rw [show Wx lam ϕ x z=0 from if_pos hzL,sub_zero]
        exact (mul_nonpos_of_nonneg_of_nonpos hxφ.le (lowK q z hq hqp hpz hz hpos)).trans
          (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      · have hs := (gPhi_properties hϕ).2.1 z ⟨le_of_not_ge hzL,hz⟩
        have hc : (1+B*p)*ϕ x ≤ (lam-x)+C x := by
          have hh := le_max_left ((1+B*p)*ϕ x-(lam-x)) 0
          dsimp [C]; linarith
        have hk := mul_le_mul_of_nonneg_left (H.2 _ _ _ hq hqp hpz hz) hB
        have hthree := hϕ.le_lam_sub z ⟨hp.1.le.trans hpz,hz⟩
        have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB hq) hs
        have hb : q+z-lam+B*KP ϕ p q z+(1+B*p)*ϕ z ≤ 0 := by
          nlinarith only [hk,hthree,hn,jbound q hq hqp]
        have hg := mul_nonpos_of_nonneg_of_nonpos hxφ.le hb
        have hmul := mul_le_mul_of_nonpos_right hc hs
        rw [Wx,if_neg hzL,max_eq_left (neg_nonneg.mpr hs)]
        have hcancel : ϕ x*((lam-x)/ϕ x)=lam-x := by field_simp
        nlinarith only [hg,hmul,congrArg (fun r => r*ϕ z) hcancel]

end StableVotingDistortion
end


open StableVotingDistortion

theorem solution :
    ∀ {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p0 : ℝ} (hp0 : 0 < p0) (hp0lam : p0 < lam) {β0 : ℝ} (hβ0 : 0 < β0)
    (h45a : 1 ≤ β0 * ϕ p0) (h45b : p0 * (1 + β0 * (1 + ϕ 0)) ≤ lam)
    (h45c : ∀ x ∈ Set.Icc 0 lam, p0 * (1 - β0 * (ϕ p0 - ϕ x)) ≤ sigma lam ϕ x),
    ∀ p ∈ Set.Ioc 0 p0,
      Eq37 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p ∧
        Eq38 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p :=
  @StableVotingDistortion.lemma_14_i
