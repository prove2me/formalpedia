-- Prove2me | solution 1 for StableVotingDistortion.lemma_14_ii
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:21.808184+00:00
-- url     : https://prove2.me/submissions/a076a0d5-40cb-4034-b51a-cc5bf2f7e360

import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_VerifierHypotheses
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Mathlib

-- Source module ConcaveIncrements
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

/-- Equal-length increments of a concave function decrease from left to right. -/
theorem concave_increment_antitone {lam : ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc lam 1) f)
    {x y s : ℝ} (hx : lam ≤ x) (hxy : x ≤ y) (hs : 0 ≤ s) (hy : y+s ≤ 1) :
    f (y+s)-f y ≤ f (x+s)-f x := by
  rcases hs.eq_or_lt with rfl | hpos
  · simp
  let T := y+s-x
  have hT : 0<T := by dsimp [T]; linarith
  let u := s/T
  have hue : u*T=s := div_mul_cancel₀ _ hT.ne'
  have hu : 0 ≤ u := div_nonneg hpos.le hT.le
  have hv : 0 ≤ 1-u := sub_nonneg.mpr ((div_le_one hT).mpr (by dsimp [T]; linarith))
  have hxm : x ∈ Icc lam 1 := ⟨hx,by linarith⟩
  have hym : y+s ∈ Icc lam 1 := ⟨by linarith,hy⟩
  have h1 := hf.2 hxm hym hv hu (by ring)
  have h2 := hf.2 hxm hym hu hv (by ring)
  simp only [smul_eq_mul] at h1 h2
  dsimp only [T] at hue
  have hx' : (1-u)*x+u*(y+s)=x+s := by nlinarith only [hue]
  have hy' : u*x+(1-u)*(y+s)=y := by nlinarith only [hue]
  rw [hx'] at h1; rw [hy'] at h2
  linarith only [h1,h2]

/-- Express a primitive increment on a translated interval by an integral over the offset. -/
theorem J_increment {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a+s ≤ 1) :
    J ϕ (a+s)-J ϕ a = ∫ u in (0:ℝ)..s, ϕ (a+u) := by
  have ai {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :=
    (h.continuousOn.mono (Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc (μ := volume) hxy
  have had := intervalIntegral.integral_add_adjacent_intervals (ai (le_refl 0) ha (by linarith))
    (ai ha (by linarith : a ≤ a+s) has)
  unfold J
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero,zero_add] at *
  linarith

end StableVotingDistortion
end

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

-- Source module HighTailConcavity
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

/-- At high q, one test at λ suffices by concavity; a nonnegative constant
penalty and beta times primitive at least p are both allowed. -/
theorem high_tail_penalty {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    (hconc : ConcaveOn ℝ (Icc lam 1) ϕ) (hadd : AntitoneOn (fun x => ϕ x+x) (Icc lam 1))
    {p q z B R penalty : ℝ} (hp : p ∈ Ioo lam 1) (hq : q ∈ Icc lam p) (hz : z ∈ Icc p 1)
    (hB : 0 ≤ B) (hBJ : p ≤ B*J ϕ p) (hR : 1 ≤ R)
    (hpen : 0 ≤ penalty) (hbase : z+B*KP ϕ p lam z+R*ϕ z-penalty ≤ 0)
    (hzero : ϕ lam=0) :
    z+B*KP ϕ p q z-R*(ϕ q-ϕ z)-penalty ≤ 0 := by
  let s := z-p
  have hs : 0 ≤ s := sub_nonneg.mpr hz.1
  have hsz : p+s=z := by dsimp [s];ring
  have hm (a : ℝ) (ha : a ∈ Icc lam p) : a+s ∈ Icc lam 1 := ⟨by linarith [ha.1],by linarith [ha.2,hz.2,hsz]⟩
  have hInt (a : ℝ) (ha : a ∈ Icc lam p) : IntervalIntegrable (fun u => ϕ (a+u)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs
    apply h.continuousOn.comp (f := fun u : ℝ => a+u) (by fun_prop)
    intro u hu
    exact ⟨by linarith [ha.1,h.lam_mem.1,hu.1],by linarith [ha.2,hu.2,hz.2,hsz]⟩
  have hK (a : ℝ) (ha : a ∈ Icc lam p) : KP ϕ p a z =
      (∫ u in (0:ℝ)..s, (ϕ (a+u)-ϕ (p+u))) - J ϕ p := by
    rw [intervalIntegral.integral_sub (hInt a ha) (hInt p ⟨hp.1.le,le_rfl⟩),
      ← J_increment h (h.lam_mem.1.le.trans ha.1) hs (hm a ha).2,
      ← J_increment h (h.lam_mem.1.le.trans hp.1.le) hs (by linarith [hsz,hz.2] : p+s ≤ 1), hsz]
    unfold KP
    rw [show a+s=z-p+a by dsimp [s];ring]
    ring
  let F := fun (a u : ℝ) => ϕ (a+u)-ϕ (p+u)
  have hFi (a : ℝ) (ha : a ∈ Icc lam p) : IntervalIntegrable (F a) volume 0 s := (hInt a ha).sub (hInt p ⟨hp.1.le,le_rfl⟩)
  by_cases hcut : B*s ≤ R
  · have hpoint (u : ℝ) (hu : u ∈ Icc 0 s) : F q u ≤ ϕ (q+s)-ϕ z := by
      have hi := concave_increment_antitone hconc (show lam ≤ q+u by linarith [hq.1,hu.1])
        (show q+u ≤ p+u by linarith [hq.2]) (show 0 ≤ s-u by linarith [hu.2]) (show p+u+(s-u) ≤ 1 by linarith [hsz,hz.2])
      rw [show q+u+(s-u)=q+s by ring,show p+u+(s-u)=z by linarith] at hi
      dsimp [F];linarith
    have hi := intervalIntegral.integral_mono_on hs (hFi q hq) (intervalIntegrable_const (c := ϕ (q+s)-ϕ z)) hpoint
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
    have hqsz := h.antitoneOn ⟨h.lam_mem.1.le.trans (hm q hq).1,(hm q hq).2⟩
      ⟨by linarith [hq.1,h.lam_mem.1,hq.2,hz.1],hz.2⟩ (by linarith [hq.2,hsz] : q+s ≤ z)
    have hstrict := hadd ⟨hq.1,hq.2.trans hp.2.le⟩ (hm q hq) (by linarith : q ≤ q+s)
    dsimp only at hstrict
    have h1 := mul_le_mul_of_nonneg_left hi hB
    have h2 := mul_le_mul_of_nonneg_right hcut (sub_nonneg.mpr hqsz)
    have h3 := mul_le_mul_of_nonneg_left hstrict (zero_le_one.trans hR)
    have h4 := mul_le_mul_of_nonneg_right hR hs
    rw [hK q hq]
    change z+B*((∫ u in (0:ℝ)..s,F q u)-J ϕ p)-R*(ϕ q-ϕ z)-penalty ≤ 0
    nlinarith only [h1,h2,h3,h4,hBJ,hsz,hpen]
  · have hpoint (u : ℝ) (hu : u ∈ Icc 0 s) : F q u-F lam u ≤ ϕ q := by
      have hi := concave_increment_antitone hconc (le_refl lam) hq.1 hu.1
        (show q+u ≤ 1 by linarith [hu.2,hq.2,hsz,hz.2])
      rw [hzero] at hi
      dsimp [F];linarith
    have hla : lam ∈ Icc lam p := ⟨le_rfl,hp.1.le⟩
    have hi := intervalIntegral.integral_mono_on hs ((hFi q hq).sub (hFi lam hla))
      (intervalIntegrable_const (c := ϕ q)) hpoint
    rw [intervalIntegral.integral_sub (hFi q hq) (hFi lam hla),intervalIntegral.integral_const] at hi
    simp only [sub_zero,smul_eq_mul] at hi
    have hh := mul_le_mul_of_nonneg_left hi hB
    have hu := mul_le_mul_of_nonpos_right (le_of_not_ge hcut) ((gPhi_properties h).2.1 q ⟨hq.1,hq.2.trans hp.2.le⟩)
    rw [hK q hq]; rw [hK lam hla] at hbase
    change z+B*((∫ u in (0:ℝ)..s,F q u)-J ϕ p)-R*(ϕ q-ϕ z)-penalty ≤ 0
    change z+B*((∫ u in (0:ℝ)..s,F lam u)-J ϕ p)+R*ϕ z-penalty ≤ 0 at hbase
    nlinarith only [hh,hu,hbase]

end StableVotingDistortion
end

-- Source module LargeMass
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

private theorem large_tail {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {p q z M : ℝ} (hl : lam<p) (hp : p<1) (hq : q ∈ Icc 0 lam) (hz : z ∈ Icc p 1)
    (hM : 1 ≤ M) (hJ : 0 < J ϕ p) (h25 : Eq25 lam ϕ p)
    (hline : ϕ (lam+(1-p)) = -(1-p))
    (hLip : ∀ r s, p ≤ r → r<s → s ≤ 1 → ϕ r-ϕ s ≤ M*(s-r))
    (h47 : (M-1)*J ϕ p ≤ p*(1-(M+1)*(1-p))) :
    q+z-lam+(p/J ϕ p)*KP ϕ p q z+ϕ z ≤ 0 := by
  let B := p/J ϕ p
  have hp0 := h.lam_mem.1.trans hl
  have hB : 0 < B := div_pos hp0 hJ
  have hBJ : B*J ϕ p=p := div_mul_cancel₀ _ hJ.ne'
  have hEnd : q+B*deltaP ϕ p q ≤ lam := by
    have hh := h25 q hq.1 (le_min (hq.2.trans hl.le) hq.2)
    change p * deltaP ϕ p q ≤ (lam - q) * J ϕ p at hh
    have he : B*deltaP ϕ p q * J ϕ p = p*deltaP ϕ p q := by rw [mul_right_comm,hBJ]
    apply (le_of_mul_le_mul_right _ hJ)
    nlinarith only [he,hh]
  have hE1 : q+1-lam+B*KP ϕ p q 1+ϕ 1 ≤ 0 := by
    have hk : KP ϕ p q 1=deltaP ϕ p q := by simp [KP,deltaP,J,h.integral_eq_zero]
    rw [hk,h.at_one]; linarith
  by_cases hz1 : z=1
  · subst z; exact hE1
  let d := 1-z
  have hd : 0 < d := sub_pos.mpr (lt_of_le_of_ne hz.2 hz1)
  have ha : 0 ≤ z-p+q := by linarith [hz.1,hq.1]
  have hb : 1-p+q ≤ 1 := by linarith [hq.2]
  have hlineW : lam+(1-p) ≤ 1 := by linarith
  have hc := h.antitoneOn (show 1-p+q ∈ Icc 0 1 from ⟨by linarith [hq.1],hb⟩)
    (show lam+(1-p) ∈ Icc 0 1 from ⟨by linarith [h.lam_mem.1],hlineW⟩) (by linarith [hq.2])
  rw [hline] at hc
  have hlower := (primitive_sandwich h ha (show z-p+q ≤ 1-p+q by linarith [hz.2]) hb).1
  have hupper := (primitive_sandwich h (hp0.le.trans hz.1) hz.2 (le_refl 1)).2
  have hlip := hLip z 1 hz.1 (lt_of_le_of_ne hz.2 hz1) le_rfl
  have hzphi : ϕ z ≤ -1+M*(1-p) := by rw [h.at_one] at hlip; nlinarith [mul_le_mul_of_nonneg_left (show 1-z ≤ 1-p by linarith [hz.1]) (by linarith : 0 ≤ M)]
  have hcoef : 0 ≤ 1-M+B*(1-(M+1)*(1-p)) := by
    apply le_of_mul_le_mul_right _ hJ
    nlinarith only [h47,congrArg (fun x => x*(1-(M+1)*(1-p))) hBJ]
  have hk : d*(1-(M+1)*(1-p)) ≤ KP ϕ p q 1 - KP ϕ p q z := by
    unfold KP
    dsimp [d] at hd ⊢
    nlinarith only [hlower,hupper,mul_le_mul_of_nonneg_left hc hd.le,mul_le_mul_of_nonneg_left hzphi hd.le]
  change q+z-lam+B*KP ϕ p q z+ϕ z ≤ 0
  have hg := mul_nonneg hd.le hcoef
  have hk' := mul_le_mul_of_nonneg_left hk hB.le
  dsimp only [d] at hg hk'
  nlinarith only [hE1,hg,hk',hlip]

private theorem large_high_tail {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    (hconc : ConcaveOn ℝ (Icc lam 1) ϕ) (hadd : AntitoneOn (fun x => ϕ x+x) (Icc lam 1))
    {p q z B R : ℝ} (hp : p ∈ Ioo lam 1) (hq : q ∈ Icc lam p) (hz : z ∈ Icc p 1)
    (hB : 0 ≤ B) (hBJ : B*J ϕ p=p) (hR : 1 ≤ R)
    (hbase : lam+z-lam+B*KP ϕ p lam z+ϕ z ≤ 0)
    (hzero : ϕ lam=0) :
    z+B*KP ϕ p q z-R*(ϕ q-ϕ z) ≤ 0 := by
  have hzL := (gPhi_properties h).2.1 z ⟨hp.1.le.trans hz.1,hz.2⟩
  have hv := mul_le_mul_of_nonpos_right hR hzL
  have hh := high_tail_penalty h hconc hadd hp hq hz hB hBJ.ge hR (penalty:=0) le_rfl (by linarith) hzero
  simpa using hh

theorem lemma_14_ii {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p1 : ℝ} (hp1lam : lam < p1) (hp1 : p1 < 1)
    {rm zp : ℝ} (hrm0 : 0 ≤ rm) (hzp1 : zp ≤ 1) (hrm : rm < lam) (hzp : lam + (1 - p1) ≤ zp)
    (hline : ∀ r ∈ Set.Icc rm zp, ϕ r = lam - r)
    (hconc : ConcaveOn ℝ (Set.Icc lam 1) ϕ)
    {m0 M : ℝ} (hm0 : 0 < m0) (hm01 : m0 < 1) (hM : 1 ≤ M)
    (h46a : ∀ r s, 0 ≤ r → r < s → s ≤ rm → ϕ r - ϕ s ≤ m0 * (s - r))
    (h46b : ∀ r s, p1 ≤ r → r < s → s ≤ 1 → ϕ r - ϕ s ≤ M * (s - r))
    (h25 : ∀ p ∈ Set.Ico p1 1, Eq25 lam ϕ p)
    (h47a : ∀ p ∈ Set.Ico p1 1, m0 * (p * (1 - p)) ≤ J ϕ p)
    (h47b : ∀ p ∈ Set.Ico p1 1, J ϕ p ≤ p * (1 - p))
    (h47c : ∀ p ∈ Set.Ico p1 1, (M - 1) * J ϕ p ≤ p * (1 - (M + 1) * (1 - p))) :
    ∀ p ∈ Set.Ico p1 1,
      Eq37 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p ∧
        Eq38 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p := by
  intro p hp
  let B := p/J ϕ p
  let t := B*(1-p)
  let C := fun x => max (lam-x-t*ϕ x) 0
  have hpL := hp1lam.trans_le hp.1
  have hp0 := hϕ.lam_mem.1.trans hpL
  have hF := sub_pos.mpr hp.2
  have hJ : 0 < J ϕ p := lt_of_lt_of_le (mul_pos hm0 (mul_pos hp0 hF)) (h47a p hp)
  have hB : 0 < B := div_pos hp0 hJ
  have hBJ : B*J ϕ p=p := div_mul_cancel₀ _ hJ.ne'
  have htJ : t*J ϕ p=p*(1-p) := by dsimp [t]; rw [mul_right_comm,hBJ]
  have ht1 : 1 ≤ t := by apply le_of_mul_le_mul_right _ hJ; linarith [h47b p hp]
  have ht0 := zero_le_one.trans ht1
  have htm : t*m0 ≤ 1 := by
    apply le_of_mul_le_mul_right _ hJ
    nlinarith only [h47a p hp,congrArg (fun X => m0*X) htJ]
  have hprim := eq_43_44 hϕ
  have h48 (q : ℝ) (hq : q ∈ Icc 0 lam) : q+B*deltaP ϕ p q ≤ lam := by
    have hh := h25 p hp q hq.1 (le_min (hq.2.trans hpL.le) hq.2)
    change p * deltaP ϕ p q ≤ (lam - q) * J ϕ p at hh
    have he : B*deltaP ϕ p q * J ϕ p = p*deltaP ϕ p q := by rw [mul_right_comm,hBJ]
    apply le_of_mul_le_mul_right _ hJ; nlinarith only [he,hh]
  have hΔ (q : ℝ) (hq : q ∈ Icc 0 p) : B*deltaP ϕ p q ≤ t*ϕ q := by
    have hi := mul_le_mul_of_nonneg_left (hprim.1 p q hq.1 hq.2 hp.2.le).2.1 hB.le
    simpa only [t,mul_assoc] using hi
  have hc0 (x : ℝ) : 0 ≤ C x := le_max_right _ _
  have hzero := (gPhi_properties hϕ).1
  constructor
  · intro x hx
    constructor
    · intro q hq hqm
      have hqp := hqm.trans (min_le_left _ _)
      have hqx := hqm.trans (min_le_right _ _)
      have hl := h48 q ⟨hq,hqx.trans hx.2.le⟩
      change q+B*deltaP ϕ p q+C x ≤ lam
      by_cases hr : rm ≤ x
      · have hxline := hline x ⟨hr,by linarith [hx.2,hzp]⟩
        have hc : C x=0 := by apply max_eq_right; nlinarith [mul_le_mul_of_nonneg_right ht1 (hϕ.pos x hx).le]
        rw [hc,add_zero];exact hl
      · have hlip : ϕ q-ϕ x ≤ m0*(x-q) := by
          rcases hqx.lt_or_eq with lo | eq
          · exact h46a q x hq lo (le_of_not_ge hr)
          · rw [eq];simp
        dsimp only [C];rw [add_max];apply max_le
        · have ha := mul_le_mul_of_nonneg_left hlip ht0
          have hb := mul_le_mul_of_nonneg_right htm (sub_nonneg.mpr hqx)
          nlinarith only [hΔ q ⟨hq,hqp⟩,ha,hb]
        · simpa using hl
    · intro _ _ _ hpx; linarith [hx.2]
  · intro x hx
    have hφ := hϕ.pos x hx
    let R := (lam-x)/ϕ x
    have hR : 1 ≤ R := (one_le_div hφ).mpr (hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hϕ.lam_mem.2.le⟩)
    have hcancel : ϕ x*R=lam-x := by dsimp [R];field_simp
    have hfix : ϕ (lam+(1-p)) = -(1-p) := by
      rw [hline]; ring
      exact ⟨by linarith,by linarith [hp.1]⟩
    have htail {q z : ℝ} (hq : q ∈ Icc 0 lam) (hz : z ∈ Icc p 1) :=
      large_tail hϕ hpL hp.2 hq hz hM hJ (h25 p hp) hfix (fun r s hr => h46b r s (hp.1.trans hr)) (h47c p hp)
    constructor
    · intro q hq hqp
      change ϕ x*(q+B*deltaP ϕ p q+Wx lam ϕ x q-lam) ≤ max (-ϕ q) 0*C x
      by_cases hqL : q ≤ lam
      · rw [show Wx lam ϕ x q=0 from if_pos hqL,add_zero]
        exact (mul_nonpos_of_nonneg_of_nonpos hφ.le (sub_nonpos.mpr (h48 _ ⟨hq,hqL⟩))).trans
          (mul_nonneg (le_max_right _ _) (hc0 x))
      · have hqφ := (gPhi_properties hϕ).2.1 q ⟨le_of_not_ge hqL,hqp.trans hp.2.le⟩
        rw [Wx,if_neg hqL,max_eq_left (neg_nonneg.mpr hqφ)]
        have hh := mul_le_mul_of_nonneg_left (hΔ q ⟨hq,hqp⟩) hφ.le
        have hv : lam-x-t*ϕ x ≤ C x := le_max_left _ _
        have hneg := mul_le_mul_of_nonpos_right hv hqφ
        nlinarith only [hh,hneg,congrArg (fun r => r*ϕ q) hcancel]
    · intro q z hq hqp hpz hz
      have hzL := hpL.trans_le hpz
      have hzφ := (gPhi_properties hϕ).2.1 z ⟨hzL.le,hz⟩
      change ϕ x*(q+B*KP ϕ p q z+Wx lam ϕ x q-Wx lam ϕ x z) ≤ max (-ϕ z) 0*C x
      rw [show Wx lam ϕ x z=lam-z-R*ϕ z from if_neg (not_le.mpr hzL),max_eq_left (neg_nonneg.mpr hzφ)]
      have hn := mul_nonneg (neg_nonneg.mpr hzφ) (hc0 x)
      by_cases hqL : q ≤ lam
      · have hh := htail (q := q) ⟨hq,hqL⟩ ⟨hpz,hz⟩
        have hv := mul_le_mul_of_nonpos_right hR hzφ
        have hi : q+B*KP ϕ p q z-(lam-z-R*ϕ z) ≤ 0 := by linarith
        rw [show Wx lam ϕ x q=0 from if_pos hqL,add_zero]
        exact (mul_nonpos_of_nonneg_of_nonpos hφ.le hi).trans hn
      · have hh := large_high_tail hϕ hconc hadd ⟨hpL,hp.2⟩ ⟨le_of_not_ge hqL,hqp⟩
          ⟨hpz,hz⟩ hB.le hBJ hR (htail (q := lam) ⟨hϕ.lam_mem.1.le,le_rfl⟩ ⟨hpz,hz⟩) hzero
        rw [show Wx lam ϕ x q=lam-q-R*ϕ q from if_neg hqL]
        exact (mul_nonpos_of_nonneg_of_nonpos hφ.le (by linarith)).trans hn

end StableVotingDistortion
end


open StableVotingDistortion

theorem solution :
    ∀ {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p1 : ℝ} (hp1lam : lam < p1) (hp1 : p1 < 1)
    {rm zp : ℝ} (hrm0 : 0 ≤ rm) (hzp1 : zp ≤ 1) (hrm : rm < lam) (hzp : lam + (1 - p1) ≤ zp)
    (hline : ∀ r ∈ Set.Icc rm zp, ϕ r = lam - r)
    (hconc : ConcaveOn ℝ (Set.Icc lam 1) ϕ)
    {m0 M : ℝ} (hm0 : 0 < m0) (hm01 : m0 < 1) (hM : 1 ≤ M)
    (h46a : ∀ r s, 0 ≤ r → r < s → s ≤ rm → ϕ r - ϕ s ≤ m0 * (s - r))
    (h46b : ∀ r s, p1 ≤ r → r < s → s ≤ 1 → ϕ r - ϕ s ≤ M * (s - r))
    (h25 : ∀ p ∈ Set.Ico p1 1, Eq25 lam ϕ p)
    (h47a : ∀ p ∈ Set.Ico p1 1, m0 * (p * (1 - p)) ≤ J ϕ p)
    (h47b : ∀ p ∈ Set.Ico p1 1, J ϕ p ≤ p * (1 - p))
    (h47c : ∀ p ∈ Set.Ico p1 1, (M - 1) * J ϕ p ≤ p * (1 - (M + 1) * (1 - p))),
    ∀ p ∈ Set.Ico p1 1,
      Eq37 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p ∧
        Eq38 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p :=
  @StableVotingDistortion.lemma_14_ii
