-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:37:26.339395+00:00
-- url     : https://prove2.me/submissions/2c843efd-08c0-4a91-b0a5-cb46ec2e1cca

import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral
import Mathlib

set_option autoImplicit false

-- Solutions.StratifyMarketsExponentialScale
section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace StratifyMarkets.DoubleAuction.Scale

def theta (h : ℝ) := Real.exp (-h)
def eta (h : ℝ) := Real.exp (h-1)
def primitive (Q : ℝ → ℝ) (t : ℝ) := ∫ u in 0..t, Q u

/-- BWZ26, Lemma 3.8, for the bounded, almost-everywhere continuous quantile functions
used in the bilateral theorem. The exceptional points may be any countable set. -/
theorem exponential_scale (Q : ℝ → ℝ) (meas : Measurable Q) (bound : ∀ x, ‖Q x‖ ≤ 1)
    (exc : {x | ¬ContinuousAt Q x}.Countable) (t : ℝ) (ht : 0 ≤ t) :
    (∫ h in (0:ℝ)..1, eta h * (h * primitive Q (theta h*t)
      + (1-h)*theta h*t*Q (theta h*t))) = Real.exp (-1) * primitive Q t := by
  rcases ht.eq_or_lt with rfl|positive
  · simp [primitive]
  have int (a b : ℝ) : IntervalIntegrable Q volume a b := by
    rw [intervalIntegrable_iff]
    apply (integrableOn_const (C := (1:ℝ)) (by simp [uIoc,Real.volume_Ioc])).mono' meas.aestronglyMeasurable
    exact Eventually.of_forall bound
  have lip : LipschitzWith 1 (primitive Q) := by
    apply lipschitzWith_iff_dist_le_mul.2
    intro x y
    simp only [Real.dist_eq,primitive,intervalIntegral.integral_interval_sub_left (int 0 x) (int 0 y),
      NNReal.coe_one,one_mul]
    exact (intervalIntegral.norm_integral_le_of_norm_le_const (fun a _ => bound a)).trans_eq (by simp [abs_sub_comm])
  let z (h : ℝ) := theta h*t
  let w (h : ℝ) := (1-h)*eta h
  have cz : ContDiff ℝ 1 z := by unfold z theta; fun_prop
  have cw : ContDiff ℝ 1 w := by unfold w eta; fun_prop
  have ⟨K,hK⟩ := (cz.contDiffOn (s:=uIcc (0:ℝ) 1)).exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  let A (h : ℝ) := w h * primitive Q (z h)
  have ac : AbsolutelyContinuousOnInterval A 0 1 :=
    cw.contDiffOn.absolutelyContinuousOnInterval.mul (lip.comp_lipschitzOnWith hK).absolutelyContinuousOnInterval
  have inj : Function.Injective z := by
    intro x y eq
    change Real.exp (-x)*t = Real.exp (-y)*t at eq
    have h := Real.exp_injective (mul_right_cancel₀ positive.ne' eq)
    linarith
  have good : ∀ᵐ h ∂volume, ContinuousAt Q (z h) :=
    (exc.preimage inj).ae_notMem volume |>.mono (fun h hh => not_not.mp hh)
  have der (h : ℝ) (hh : ContinuousAt Q (z h)) :
      deriv A h = -(eta h * (h * primitive Q (theta h*t) + (1-h)*theta h*t*Q (theta h*t))) := by
    have dz : HasDerivAt z (-theta h*t) h := by
      convert! ((((hasDerivAt_id h).neg.exp).mul_const t)) using 1 <;> simp [theta,z]
    have dw : HasDerivAt w (-h*eta h) h := by
      have dw' := ((hasDerivAt_const h (1:ℝ)).sub (hasDerivAt_id h)).mul (((hasDerivAt_id h).sub_const 1).exp)
      convert! dw' using 1 <;> simp [w,eta] <;> ring
    have dp := intervalIntegral.integral_hasDerivAt_right (int 0 (z h)) meas.stronglyMeasurable.stronglyMeasurableAtFilter hh
    have a := (dw.mul (dp.comp h dz)).deriv
    change deriv A h = _ at a
    rw [a]
    dsimp [w,z]
    unfold primitive
    ring
  have eq : (∫ h in (0:ℝ)..1, deriv A h) = ∫ h in (0:ℝ)..1,
      -(eta h * (h * primitive Q (theta h*t) + (1-h)*theta h*t*Q (theta h*t))) :=
    intervalIntegral.integral_congr_ae (good.mono (fun h hc _ => der h hc))
  rw [ac.integral_deriv_eq_sub,intervalIntegral.integral_neg] at eq
  simp [A,w,z,theta,eta] at eq
  exact eq.symm

end StratifyMarkets.DoubleAuction.Scale
end

-- Solutions.StratifyMarketsBilateralQuantile
section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace StratifyMarkets.DoubleAuction.Rank

abbrev U := volume.restrict (Icc (0:ℝ) 1)
instance : IsProbabilityMeasure U := ⟨by simp [U,Real.volume_Icc]⟩

def clamp (x : ℝ) := max 0 (min 1 x)
theorem clamp_mem (x) : clamp x ∈ Icc 0 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
theorem clamp_eq {x : ℝ} (h : x ∈ Icc (0:ℝ) 1) : clamp x = x := by simp [clamp,h.1,h.2]

/-- A rank parametrization includes its pushforward law and generalized inverse identity. -/
structure Quantile (μ : Measure ℝ) where
  Q : ℝ → ℝ
  mono : Monotone Q
  bounds : ∀ x, Q x ∈ Icc 0 1
  left : ∀ x ∈ Icc (0:ℝ) 1, ∀ z ∈ Icc (0:ℝ) 1, Q x ≤ z ↔ x ≤ μ.real (Iic z)
  exact_rank : ∀ x ∈ Icc (0:ℝ) 1, μ.real (Iic (Q x)) = x
  law : U.map Q = μ

theorem quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (supported : μ (Icc 0 1) = 1) : Nonempty (Quantile μ) := by
  let C (x : ℝ) := μ.real (Iic x)
  have cm : Monotone C := fun _ _ h => measureReal_mono (Iic_subset_Iic.mpr h)
  have hm : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1 := (mem_ae_iff_prob_eq_one measurableSet_Icc).2 supported
  have ctop : C 1 = 1 := by
    have m := (mem_ae_iff_prob_eq_one (measurableSet_Iic (a:=1))).1 (hm.mono (fun _ h => h.2))
    simp [C,measureReal_def,m]
  have cbot : C 0 = 0 := by
    have e : Iic (0:ℝ) =ᵐ[μ] (∅ : Set ℝ) := by
      filter_upwards [hm,μ.ae_ne 0] with c h ne
      apply propext
      change c ≤ 0 ↔ False
      simp [show ¬ c ≤ 0 by grind [h.1]]
    simp [C,measureReal_congr e]
  have cont : ContinuousOn C (Icc (0:ℝ) 1) := by
    have hint : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic 1) μ := (integrable_const 1).integrableOn
    apply ContinuousOn.mono (s:=Iic (1:ℝ)) _ (fun _ h => h.2)
    change ContinuousOn (fun x => μ.real (Iic x)) (Iic 1)
    simpa only [setIntegral_one_eq_measureReal] using hint.continuousOn_Iic_primitive_Iic
  let S (x : ℝ) := Icc (0:ℝ) 1 ∩ C ⁻¹' Ici (clamp x)
  have non (x) : (S x).Nonempty := ⟨1,⟨⟨zero_le_one,le_rfl⟩,(clamp_mem x).2.trans_eq ctop.symm⟩⟩
  have closed (x) : IsClosed (S x) := (cont.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc _).isClosed
  have bdd (x) : BddBelow (S x) := ⟨0,fun _ h => h.1.1⟩
  let Q (x : ℝ) := sInf (S x)
  have good (x) : Q x ∈ S x := (closed x).csInf_mem (non x) (bdd x)
  have qmono : Monotone Q := by
    intro x y h
    apply csInf_le (bdd x)
    refine ⟨(good y).1,?_⟩
    have : clamp x ≤ clamp y := max_le_max_left _ (min_le_min_left _ h)
    exact this.trans (good y).2
  have left (x) (hx : x ∈ Icc (0:ℝ) 1) (z) (hz : z ∈ Icc (0:ℝ) 1) : Q x ≤ z ↔ x ≤ C z := by
    constructor
    · exact fun h => (clamp_eq hx).ge.trans ((good x).2.trans (cm h))
    · intro h
      exact csInf_le (bdd _) ⟨hz,(clamp_eq hx).le.trans h⟩
  have exact_rank (x) (hx : x ∈ Icc (0:ℝ) 1) : C (Q x) = x := by
    have pre := intermediate_value_Icc zero_le_one cont (show x ∈ Icc (C 0) (C 1) by simpa [cbot,ctop] using hx)
    obtain ⟨z,hz,ze⟩ := pre
    exact le_antisymm ((cm ((left x hx z hz).2 ze.ge)).trans_eq ze) ((left x hx (Q x) (good x).1).1 le_rfl)
  refine ⟨⟨Q,qmono,fun x => (good x).1,left,exact_rank,?_⟩⟩
  apply Measure.ext_of_Iic
  intro z
  rw [Measure.map_apply qmono.measurable measurableSet_Iic,Measure.restrict_apply (qmono.measurable measurableSet_Iic)]
  rcases lt_or_ge z 0 with neg|hz
  · have emp : Q ⁻¹' Iic z ∩ Icc 0 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x h; exact neg.not_ge ((good x).1.1.trans h.1)
    have e : Iic z =ᵐ[μ] (∅ : Set ℝ) := hm.mono (fun x h => by apply propext; change x ≤ z ↔ False; simp [show ¬x ≤ z by linarith [h.1]])
    simp [emp,measure_congr e]
  rcases lt_or_ge 1 z with top|hz'
  · have all : Q ⁻¹' Iic z ∩ Icc 0 1 = Icc 0 1 :=
      inter_eq_right.mpr (fun x _ => (good x).1.2.trans top.le)
    have m := (mem_ae_iff_prob_eq_one (measurableSet_Iic (a:=z))).1 (hm.mono fun _ h => h.2.trans top.le)
    simp [all,Real.volume_Icc,m]
  · have cq : C z ∈ Icc 0 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
    have cap : Q ⁻¹' Iic z ∩ Icc 0 1 = Icc 0 (C z) := by
      ext x
      constructor
      · intro h
        exact ⟨h.2.1,(left x h.2 z ⟨hz,hz'⟩).1 h.1⟩
      · intro h
        have hx : x ∈ Icc (0:ℝ) 1 := ⟨h.1,h.2.trans cq.2⟩
        exact ⟨(left x hx z ⟨hz,hz'⟩).2 h.2,hx⟩
    simp [cap,Real.volume_Icc,C,measureReal_def]

end StratifyMarkets.DoubleAuction.Rank
end

-- Solutions.StratifyMarketsRankCalculus
section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace StratifyMarkets.DoubleAuction.Rank
open Scale

def mean (f : ℝ → ℝ) := ∫ x, f x ∂U

theorem mean_eq_interval (f : ℝ → ℝ) : mean f = ∫ x in (0:ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact integral_Icc_eq_integral_Ioc

theorem mean_const (c : ℝ) : mean (fun _ => c) = c := by simp [mean]

theorem mean_clamp (f : ℝ → ℝ) : mean (fun x => f (clamp x)) = mean f := by
  apply integral_congr_ae
  exact (ae_restrict_mem measurableSet_Icc).mono (fun _ h => congrArg f (clamp_eq h))

theorem mean_swap (f : ℝ × ℝ → ℝ) (fm : Measurable f) (C : ℝ)
    (bound : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, ‖f (x,y)‖ ≤ C) :
    mean (fun x => mean (fun y => f (x,y))) = mean (fun y => mean (fun x => f (x,y))) := by
  have fg : Integrable f (U.prod U) := by
    apply (integrable_const (μ:=U.prod U) C).mono' fm.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le fm.norm measurable_const)).2
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc (s:=Icc (0:ℝ) 1)] with x hx
    exact (ae_restrict_mem measurableSet_Icc).mono (fun y hy => bound x hx y hy)
  exact (integral_prod f fg).symm.trans (integral_prod_symm f fg)

theorem mean_meas (f : ℝ × ℝ → ℝ) (fm : Measurable f) :
    Measurable (fun h => mean (fun t => f (h,t))) :=
  fm.stronglyMeasurable.integral_prod_right'.measurable

theorem mean_int {f : ℝ → ℝ} (m : Measurable f) {C : ℝ}
    (bound : ∀ x ∈ Icc (0:ℝ) 1, ‖f x‖ ≤ C) : Integrable f U :=
  (integrable_const C).mono' m.aestronglyMeasurable ((ae_restrict_mem measurableSet_Icc).mono bound)

theorem mean_bound {f : ℝ → ℝ} {C : ℝ} (bound : ∀ x ∈ Icc (0:ℝ) 1, ‖f x‖ ≤ C) :
    ‖mean f‖ ≤ C := by
  simpa [mean] using norm_integral_le_of_norm_le_const (μ:=U) ((ae_restrict_mem measurableSet_Icc).mono bound)

theorem mean_reflect (f : ℝ → ℝ) : mean (fun x => f (1-x)) = mean f := by
  rw [mean_eq_interval,mean_eq_interval,intervalIntegral.integral_comp_sub_left]
  norm_num

theorem mean_scale_le {f : ℝ → ℝ} (m : Measurable f) {C s : ℝ} (s0 : 0 ≤ s) (s1 : s ≤ 1)
    (bound : ∀ x ∈ Icc (0:ℝ) 1, ‖f x‖ ≤ C) (pos : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) :
    s * mean (fun x => f (s*x)) ≤ mean f := by
  rw [mean_eq_interval,mean_eq_interval]
  have eq := intervalIntegral.smul_integral_comp_mul_left (a:=(0:ℝ)) (b:=1) f s
  simp only [smul_eq_mul,mul_zero,mul_one] at eq
  rw [eq]
  have hint (a b : ℝ) (a0 : 0 ≤ a) (ab : a ≤ b) (b1 : b ≤ 1) : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff,uIoc_of_le ab]
    apply (integrableOn_const (C:=C) (by simp [Real.volume_Ioc])).mono' m.aestronglyMeasurable
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun x h => bound x ⟨a0.trans h.1.le,h.2.trans b1⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s le_rfl s0 s1) (hint s 1 s0 s1 le_rfl)]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg s1 (fun x hx => pos x ⟨s0.trans hx.1,hx.2⟩))

theorem mean_indicator (f : ℝ → ℝ) {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    mean (fun x => if x ≤ a then f x else 0) = primitive f a := by
  change (∫ x, (Iic a).indicator f x ∂U) = _
  rw [integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have s : Iic a ∩ Icc (0:ℝ) 1 = Icc 0 a := by ext x; simp only [mem_inter_iff,mem_Iic,mem_Icc];grind [ha.2]
  rw [s,integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le ha.1).symm

theorem scale_indicator (f : ℝ → ℝ) {a s : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    s * mean (fun x => if x ≤ a then f (s*x) else 0) = primitive f (s*a) := by
  rw [mean_indicator _ ha]
  simpa [primitive,smul_eq_mul] using intervalIntegral.smul_integral_comp_mul_left (a:=(0:ℝ)) (b:=a) f s

theorem primitive_meas {f : ℝ → ℝ} (fm : Measurable f) {C : ℝ} (bound : ∀ x, ‖f x‖ ≤ C) : Measurable (primitive f) := by
  apply (intervalIntegral.continuous_primitive _ 0).measurable
  intro a b
  rw [intervalIntegrable_iff]
  apply (integrableOn_const (C:=C) (by simp [uIoc,Real.volume_Ioc])).mono' fm.aestronglyMeasurable
  exact Eventually.of_forall bound

end StratifyMarkets.DoubleAuction.Rank
end

-- Solutions.StratifyMarketsRankRegion
section
open MeasureTheory Set Filter
noncomputable section
namespace StratifyMarkets.DoubleAuction.Rank
open Scale

/-- The horizontal and vertical quantile lengths of the efficient-trade region. -/
structure Region (I : BTInstance) where
  B : ℝ → ℝ
  S : ℝ → ℝ
  T : ℝ → ℝ
  L : ℝ → ℝ
  bm : Antitone B
  sm : Monotone S
  tm : Antitone T
  lm : Antitone L
  bb : ∀ x, B x ∈ Icc 0 1
  sb : ∀ y, S y ∈ Icc 0 1
  tb : ∀ y, T y ∈ Icc 0 1
  lb : ∀ x, L x ∈ Icc 0 1
  blaw : U.map B = I.μB
  slaw : U.map S = I.μS
  buyer_tail : ∀ x ∈ Icc (0:ℝ) 1, I.Fbar (B x) = x
  seller_cdf : ∀ y ∈ Icc (0:ℝ) 1, I.G (S y) = y
  vertical : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, (y ≤ L x ↔ S y ≤ B x)
  horizontal : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, x ≠ T y → (x ≤ T y ↔ S y ≤ B x)

theorem region (I : BTInstance) : Nonempty (Region I) := by
  letI := I.isProb_B
  letI := I.noAtoms_B
  letI := I.isProb_S
  letI := I.noAtoms_S
  obtain ⟨b⟩ := quantile I.μB I.support_B
  obtain ⟨s⟩ := quantile I.μS I.support_S
  let B (x : ℝ) := b.Q (1-x)
  let S := s.Q
  let T (y : ℝ) := I.Fbar (S y)
  let L (x : ℝ) := I.G (B x)
  have bm : Antitone B := fun _ _ h => b.mono (sub_le_sub_left h _)
  have tail : Antitone I.Fbar := fun _ _ h => measureReal_mono (Ici_subset_Ici.mpr h)
  have cdf : Monotone I.G := fun _ _ h => measureReal_mono (Iic_subset_Iic.mpr h)
  have comp (z) : I.Fbar z = 1 - I.μB.real (Iic z) := by
    change I.μB.real (Ici z) = _
    rw [← measureReal_congr (μ:=I.μB) Ioi_ae_eq_Ici,← compl_Iic,probReal_compl_eq_one_sub measurableSet_Iic]
  have blaw : U.map B = I.μB := by
    let f (x : ℝ) := 1-x
    have mf : Measurable f := measurable_const.sub measurable_id
    have fp : U.map f = U := by
      apply Measure.ext_of_Iic
      intro a
      rw [Measure.map_apply mf measurableSet_Iic]
      have pre : f ⁻¹' Iic a = Ici (1-a) := by ext z; change 1-z ≤ a ↔ 1-a ≤ z; grind
      rw [pre,Measure.restrict_apply measurableSet_Ici,Measure.restrict_apply measurableSet_Iic]
      have s1 : Ici (1-a) ∩ Icc 0 1 = Icc (max (1-a) 0) 1 := by ext x; simp [and_assoc,and_left_comm]
      have s2 : Iic a ∩ Icc 0 1 = Icc 0 (min a 1) := by ext x; simp [and_assoc,and_left_comm]
      rw [s1,s2,Real.volume_Icc,Real.volume_Icc]
      congr 1
      by_cases a ≤ 1 <;> simp [max_def,min_def] <;> split_ifs <;> linarith
    change U.map (b.Q ∘ f) = I.μB
    rw [← Measure.map_map b.mono.measurable mf,fp,b.law]
  refine ⟨⟨B,S,T,L,bm,s.mono,tail.comp_monotone s.mono,cdf.comp_antitone bm,
    fun x => b.bounds _,s.bounds,fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩,
    fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩,blaw,s.law,?_,s.exact_rank,?_,?_⟩⟩
  · intro x hx
    have h : 1-x ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.2],by linarith [hx.1]⟩
    rw [comp,b.exact_rank _ h]
    ring
  · intro x _ y hy
    exact (s.left _ hy _ (b.bounds _)).symm
  · intro x hx y hy ne
    have h : 1-x ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.2],by linarith [hx.1]⟩
    have e := b.left (1-x) h (S y) (s.bounds y)
    have eq := b.exact_rank _ h
    change x ≠ I.Fbar (S y) at ne
    change x ≤ I.Fbar (S y) ↔ S y ≤ b.Q (1-x)
    rw [comp] at ne ⊢
    constructor
    · intro small
      by_contra! bad
      have H := e.1 bad.le
      apply ne
      linarith
    · intro hle
      have H : I.μB.real (Iic (S y)) ≤ I.μB.real (Iic (b.Q (1-x))) :=
        measureReal_mono (Iic_subset_Iic.mpr hle)
      linarith

namespace Region
private theorem unit_ne (z : ℝ) : ∀ᵐ x ∂U, x ≠ z := U.ae_ne z

theorem transpose {I : BTInstance} (R : Region I) (f : ℝ × ℝ → ℝ) (fm : Measurable f) (C : ℝ)
    (bound : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, ‖f (x,y)‖ ≤ C) (cn : 0 ≤ C) :
    mean (fun y => mean (fun x => if x ≤ R.T y then f (x,y) else 0)) =
    mean (fun x => mean (fun y => if y ≤ R.L x then f (x,y) else 0)) := by
  calc
    _ = mean (fun y => mean (fun x => if y ≤ R.L x then f (x,y) else 0)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc (s:=Icc (0:ℝ) 1)] with y hy
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc (s:=Icc (0:ℝ) 1),unit_ne (R.T y)] with x hx ne
      simp only [(R.horizontal x hx y hy ne).trans (R.vertical x hx y hy).symm]
    _ = _ := (mean_swap (fun z => if z.2 ≤ R.L z.1 then f z else 0)
      (Measurable.ite (measurableSet_le measurable_snd (R.lm.measurable.comp measurable_fst)) fm measurable_const) C
      (fun x hx y hy => by split <;> simp_all)).symm

end Region
end StratifyMarkets.DoubleAuction.Rank
end

-- Solutions.StratifyMarketsRankScale
section
open MeasureTheory Set Filter
noncomputable section
namespace StratifyMarkets.DoubleAuction.Rank
open Scale

theorem theta_unit {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) : theta h ∈ Icc (0:ℝ) 1 :=
  ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh.1)⟩
theorem eta_unit {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) : eta h ∈ Icc (0:ℝ) 1 :=
  ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (sub_nonpos.mpr hh.2)⟩
theorem mul_unit {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) : x*y ∈ Icc (0:ℝ) 1 :=
  ⟨mul_nonneg hx.1 hy.1,(mul_le_mul_of_nonneg_right hx.2 hy.1).trans (by simpa using hy.2)⟩
theorem norm_unit {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : ‖x‖ ≤ 1 := by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2

theorem primitive_unit {Q : ℝ → ℝ} (Qb : ∀ x, Q x ∈ Icc 0 1) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    primitive Q x ∈ Icc 0 1 := by
  refine ⟨intervalIntegral.integral_nonneg hx.1 (fun u _ => (Qb u).1),?_⟩
  have lim := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=x) (fun z _ => norm_unit (Qb z))
  simp [abs_of_nonneg hx.1] at lim
  exact (le_abs_self _).trans (lim.trans hx.2)

def edge (Q T : ℝ → ℝ) (h : ℝ) := mean (fun y => theta h*T y*Q (theta h*T y))
def area (Q T : ℝ → ℝ) (h : ℝ) := mean (fun y => primitive Q (theta h*T y))
def full (Q T : ℝ → ℝ) := mean (fun y => primitive Q (T y))

theorem scale_mean (Q T : ℝ → ℝ) (qm : Measurable Q) (tm : Measurable T)
    (qb : ∀ x, Q x ∈ Icc 0 1) (tb : ∀ y, T y ∈ Icc 0 1) (exc : {x | ¬ContinuousAt Q x}.Countable) :
    mean (fun h => eta h * ((1-h)*edge Q T h + h*area Q T h)) =
      Real.exp (-1) * full Q T := by
  let F (z : ℝ × ℝ) := eta z.1 * ((1-z.1)*(theta z.1*T z.2*Q (theta z.1*T z.2)) +
        z.1*primitive Q (theta z.1*T z.2))
  have prim := primitive_meas qm (fun q => norm_unit (qb q))
  have tmeas : Measurable theta := by unfold theta; fun_prop
  have em : Measurable eta := by unfold eta; fun_prop
  have fm : Measurable F := by unfold F; fun_prop
  have fb (h : ℝ) (hh : h ∈ Icc (0:ℝ) 1) (y : ℝ) (_ : y ∈ Icc (0:ℝ) 1) : ‖F (h,y)‖ ≤ 2 := by
    have x := mul_unit (theta_unit hh) (tb y)
    have u := mul_unit x (qb (theta h*T y))
    have v := primitive_unit qb x
    have a := mul_unit (show 1-h ∈ Icc (0:ℝ) 1 by constructor <;> linarith [hh.1,hh.2]) u
    have b := mul_unit hh v
    let H := eta_unit hh
    have p := mul_nonneg H.1 (add_nonneg a.1 b.1)
    unfold F
    simp only [Real.norm_eq_abs,abs_of_nonneg p]
    nlinarith [mul_le_mul_of_nonneg_right H.2 (add_nonneg a.1 b.1),a.2,b.2]
  calc
    _ = mean (fun h => mean (fun y => F (h,y))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc (s:=Icc (0:ℝ) 1)] with h hh
      have e : Integrable (fun y => theta h*T y*Q (theta h*T y)) U :=
        mean_int (by fun_prop) (fun y _ => norm_unit (mul_unit (mul_unit (theta_unit hh) (tb y)) (qb _)))
      have a : Integrable (fun y => primitive Q (theta h*T y)) U :=
        mean_int (by fun_prop) (fun y _ => norm_unit (primitive_unit qb (mul_unit (theta_unit hh) (tb y))))
      unfold F edge area mean
      dsimp only
      rw [integral_const_mul,integral_add ((e.const_mul (1-h))) (a.const_mul h),integral_const_mul,integral_const_mul]
    _ = mean (fun y => mean (fun h => F (h,y))) := mean_swap F fm 2 fb
    _ = _ := by
      unfold full mean
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change mean (fun h => F (h,y)) = _
      rw [mean_eq_interval]
      calc
        _ = ∫ h in (0:ℝ)..1, eta h*(h*primitive Q (theta h*T y) + (1-h)*theta h*T y*Q (theta h*T y)) := by
          apply intervalIntegral.integral_congr;intro h _;dsimp [F];ring
        _ = _ := exponential_scale Q qm (fun x => norm_unit (qb x)) exc (T y) (tb y).1

namespace Region

theorem areaB {I : BTInstance} (R : Region I) (h : ℝ) :
    area R.B R.T h = theta h * mean (fun x => R.L x * R.B (theta h*x)) := by
  have eq := R.transpose (fun z => R.B (theta h*z.1))
    (R.bm.measurable.comp (measurable_const.mul measurable_fst)) 1 (fun x _ y _ => norm_unit (R.bb _)) zero_le_one
  unfold area
  calc
    _ = theta h * mean (fun y => mean (fun x => if x ≤ R.T y then R.B (theta h*x) else 0)) := by
      unfold mean
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => (scale_indicator R.B (R.tb y)).symm)
    _ = _ := by
      rw [eq]
      apply congrArg (fun v => theta h*v)
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp only; rw [mean_indicator (fun _ => R.B (theta h*x)) (R.lb x)];simp [primitive,smul_eq_mul])

theorem areaS {I : BTInstance} (R : Region I) (h : ℝ) :
    area R.S R.L h = theta h * mean (fun y => R.T y * R.S (theta h*y)) := by
  have eq := R.transpose (fun z => R.S (theta h*z.2))
    (R.sm.measurable.comp (measurable_const.mul measurable_snd)) 1 (fun x _ y _ => norm_unit (R.sb _)) zero_le_one
  unfold area
  calc
    _ = theta h * mean (fun x => mean (fun y => if y ≤ R.L x then R.S (theta h*y) else 0)) := by
      unfold mean
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => (scale_indicator R.S (R.lb x)).symm)
    _ = _ := by
      rw [← eq]
      apply congrArg (fun v => theta h*v)
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by dsimp only; rw [mean_indicator (fun _ => R.S (theta h*y)) (R.tb y)];simp [primitive,smul_eq_mul])

end Region
end StratifyMarkets.DoubleAuction.Rank
end

-- Solutions.StratifyMarketsRankProfits
section
open MeasureTheory Set Filter
noncomputable section
namespace StratifyMarkets.DoubleAuction.Rank
open Scale

private theorem seller_bdd (I : BTInstance) (c : ℝ) : BddAbove
    (Set.range fun s : Icc (0:ℝ) 1 => ((s:ℝ)-c)*I.Fbar s) := by
  letI := I.isProb_B
  refine ⟨1+|c|,?_⟩
  rintro _ ⟨s,rfl⟩
  have h : I.Fbar s ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  have cost : (s:ℝ)-c ≤ 1+|c| := by linarith [s.2.2,neg_le_abs c]
  exact (mul_le_mul_of_nonneg_right cost h.1).trans (by nlinarith [mul_le_mul_of_nonneg_left h.2 (show 0 ≤ 1+|c| by positivity)])

private theorem buyer_bdd (I : BTInstance) (v : ℝ) : BddAbove
    (Set.range fun s : Icc (0:ℝ) 1 => (v-(s:ℝ))*I.G s) := by
  letI := I.isProb_S
  refine ⟨|v|,?_⟩
  rintro _ ⟨s,rfl⟩
  have h : I.G s ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  have cost : v-(s:ℝ) ≤ |v| := by linarith [s.2.1,le_abs_self v]
  exact (mul_le_mul_of_nonneg_right cost h.1).trans (by nlinarith [mul_le_mul_of_nonneg_left h.2 (abs_nonneg v)])

theorem offerSeller (I : BTInstance) (c : ℝ) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    (s-c)*I.Fbar s ≤ I.sellerProfitAt c := le_ciSup (seller_bdd I c) (⟨s,hs⟩ : Icc (0:ℝ) 1)
theorem offerBuyer (I : BTInstance) (v : ℝ) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    (v-s)*I.G s ≤ I.buyerProfitAt v := le_ciSup (buyer_bdd I v) (⟨s,hs⟩ : Icc (0:ℝ) 1)

theorem seller_meas (I : BTInstance) : Measurable I.sellerProfitAt := by
  apply Antitone.measurable
  intro x y h
  apply ciSup_le
  intro s
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left h _) (ENNReal.toReal_nonneg)).trans (offerSeller I x s s.2)

theorem buyer_meas (I : BTInstance) : Measurable I.buyerProfitAt := by
  apply Monotone.measurable
  intro x y h
  apply ciSup_le
  intro s
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right h _) (ENNReal.toReal_nonneg)).trans (offerBuyer I y s s.2)

theorem seller_unit (I : BTInstance) {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) : I.sellerProfitAt c ∈ Icc 0 1 := by
  letI := I.isProb_B
  constructor
  · simpa using offerSeller I c c hc
  · apply ciSup_le
    intro s
    have h : I.Fbar s ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
    have u : (s:ℝ)-c ≤ 1 := by linarith [s.2.2,hc.1]
    exact (mul_le_mul_of_nonneg_right u h.1).trans (by simpa using h.2)

theorem buyer_unit (I : BTInstance) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : I.buyerProfitAt v ∈ Icc 0 1 := by
  letI := I.isProb_S
  constructor
  · simpa using offerBuyer I v v hv
  · apply ciSup_le
    intro s
    have h : I.G s ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
    have u : v-(s:ℝ) ≤ 1 := by linarith [s.2.1,hv.2]
    exact (mul_le_mul_of_nonneg_right u h.1).trans (by simpa using h.2)

theorem mean_sub {f g : ℝ → ℝ} (fi : Integrable f U) (gi : Integrable g U) :
    mean (fun x => f x-g x) = mean f-mean g := integral_sub fi gi
theorem mean_mul (a : ℝ) (f : ℝ → ℝ) : mean (fun x => a*f x) = a*mean f := integral_const_mul a f
theorem mean_ge {f g : ℝ → ℝ} (fi : Integrable f U) (gi : Integrable g U)
    (le : ∀ x ∈ Icc (0:ℝ) 1, f x ≤ g x) : mean f ≤ mean g :=
  integral_mono_ae fi gi ((ae_restrict_mem measurableSet_Icc).mono le)

namespace Region

def sellerTest {I : BTInstance} (R : Region I) (h : ℝ) := eta h * mean (fun y =>
  theta h*R.T y * (R.B (theta h*R.T y) - R.S (eta h*y)))
def buyerTest {I : BTInstance} (R : Region I) (h : ℝ) := theta h * mean (fun x =>
  eta h*R.L x * (R.B (theta h*x) - R.S (eta h*R.L x)))

private theorem norm_offer {a b c : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1)
    (hc : c ∈ Icc (0:ℝ) 1) : ‖a*(b-c)‖ ≤ 1 := by
  rw [norm_mul]
  apply (mul_le_mul (norm_unit ha) (show ‖b-c‖ ≤ 1 by rw [Real.norm_eq_abs,abs_le];constructor <;> linarith [hb.1,hb.2,hc.1,hc.2]) (norm_nonneg _) zero_le_one).trans
  norm_num

theorem seller_test_le {I : BTInstance} (R : Region I) {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) :
    R.sellerTest h ≤ I.sellerProfit := by
  let f (y : ℝ) := I.sellerProfitAt (R.S y)
  have fm : Measurable f := (seller_meas I).comp R.sm.measurable
  have fu (x) : f x ∈ Icc (0:ℝ) 1 := seller_unit I (R.sb x)
  have law : mean f = I.sellerProfit := by
    change _ = ∫ c, I.sellerProfitAt c ∂I.μS
    rw [← R.slaw,integral_map R.sm.measurable.aemeasurable (seller_meas I).aestronglyMeasurable]
    rfl
  have tm := R.tm.measurable
  have bm := R.bm.measurable
  have sm := R.sm.measurable
  let A (y : ℝ) := theta h*R.T y
  have ab (y) := mul_unit (theta_unit hh) (R.tb y)
  unfold sellerTest
  calc
    _ ≤ eta h * mean (fun y => f (eta h*y)) := by
      apply mul_le_mul_of_nonneg_left _ (eta_unit hh).1
      apply mean_ge (mean_int (by fun_prop) (fun y _ => norm_offer (ab y) (R.bb _) (R.sb _)))
        (mean_int (by fun_prop) (fun y _ => norm_unit (fu _)))
      intro y _
      have p := offerSeller I (R.S (eta h*y)) (R.B (A y)) (R.bb _)
      rw [R.buyer_tail _ (ab y),mul_comm] at p
      exact p
    _ ≤ mean f := mean_scale_le fm (eta_unit hh).1 (eta_unit hh).2 (fun x _ => norm_unit (fu x)) (fun x _ => (fu x).1)
    _ = _ := law

theorem buyer_test_le {I : BTInstance} (R : Region I) {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) :
    R.buyerTest h ≤ I.buyerProfit := by
  let f (x : ℝ) := I.buyerProfitAt (R.B x)
  have fm : Measurable f := (buyer_meas I).comp R.bm.measurable
  have fu (x) : f x ∈ Icc (0:ℝ) 1 := buyer_unit I (R.bb x)
  have law : mean f = I.buyerProfit := by
    change _ = ∫ v, I.buyerProfitAt v ∂I.μB
    rw [← R.blaw,integral_map R.bm.measurable.aemeasurable (buyer_meas I).aestronglyMeasurable]
    rfl
  have lm := R.lm.measurable
  have bm := R.bm.measurable
  have sm := R.sm.measurable
  let A (x : ℝ) := eta h*R.L x
  have ab (x) := mul_unit (eta_unit hh) (R.lb x)
  unfold buyerTest
  calc
    _ ≤ theta h * mean (fun x => f (theta h*x)) := by
      apply mul_le_mul_of_nonneg_left _ (theta_unit hh).1
      apply mean_ge (mean_int (by fun_prop) (fun x _ => norm_offer (ab x) (R.bb _) (R.sb _)))
        (mean_int (by fun_prop) (fun x _ => norm_unit (fu _)))
      intro x _
      have p := offerBuyer I (R.B (theta h*x)) (R.S (A x)) (R.sb _)
      rw [R.seller_cdf _ (ab x),mul_comm] at p
      exact p
    _ ≤ mean f := mean_scale_le fm (theta_unit hh).1 (theta_unit hh).2 (fun x _ => norm_unit (fu x)) (fun x _ => (fu x).1)
    _ = _ := law

end Region
end StratifyMarkets.DoubleAuction.Rank
end

-- Solutions.StratifyMarketsRandomOfferer
section
open MeasureTheory Set Filter
noncomputable section
namespace StratifyMarkets.DoubleAuction.Rank
open Scale

theorem mean_add {f g : ℝ → ℝ} (fi : Integrable f U) (gi : Integrable g U) :
    mean (fun x => f x+g x) = mean f+mean g := integral_add fi gi

theorem mean_identity : mean (fun h : ℝ => h) = 1/2 := by
  rw [mean_eq_interval]
  norm_num [integral_id]

theorem mean_one_sub : mean (fun h : ℝ => 1-h) = 1/2 := by
  rw [mean_reflect (fun x => x),mean_identity]

theorem theta_reflect (h : ℝ) : theta (1-h) = eta h := by unfold theta eta; congr 1;ring
theorem eta_reflect (h : ℝ) : eta (1-h) = theta h := by unfold theta eta; congr 1;ring

namespace Region
variable {I : BTInstance} (R : Region I)

theorem fb_eq : I.FB = full R.B R.T - full R.S R.L := by
  letI := I.isProb_S
  letI := I.isProb_B
  let P (x : ℝ × ℝ) := max (x.2-x.1) 0
  have pm : Measurable P := (measurable_snd.sub measurable_fst).max measurable_const
  have integr : Integrable (fun x : ℝ × ℝ => P (R.S x.1,R.B x.2)) (U.prod U) := by
    apply (integrable_const (μ:=U.prod U) (1:ℝ)).mono' (pm.comp (R.sm.measurable.prodMap R.bm.measurable)).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      dsimp [P];rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (by linarith [(R.sb x.1).1,(R.bb x.2).2]) zero_le_one)
  have eq : I.FB = mean (fun y => mean (fun x => max (R.B x-R.S y) 0)) := by
    change (∫ z, P z ∂I.μS.prod I.μB) = _
    rw [← R.slaw,← R.blaw,Measure.map_prod_map _ _ R.sm.measurable R.bm.measurable,
      integral_map (R.sm.measurable.prodMap R.bm.measurable).aemeasurable pm.aestronglyMeasurable]
    exact integral_prod _ integr
  let mb (y : ℝ) := mean (fun x => if x ≤ R.T y then R.B x else 0)
  let ms (y : ℝ) := mean (fun x => if x ≤ R.T y then R.S y else 0)
  have ib (y) : Integrable (fun x => if x ≤ R.T y then R.B x else 0) U :=
    mean_int (C:=1) (Measurable.ite measurableSet_Iic R.bm.measurable measurable_const)
      (fun x _ => by split <;> first | exact norm_unit (R.bb x) | norm_num)
  have is' (y) : Integrable (fun x => if x ≤ R.T y then R.S y else 0) U :=
    mean_int (C:=1) (Measurable.ite measurableSet_Iic measurable_const measurable_const)
      (fun x _ => by split <;> first | exact norm_unit (R.sb y) | norm_num)
  have mmb : Measurable mb := mean_meas (fun z => if z.2 ≤ R.T z.1 then R.B z.2 else 0)
    (Measurable.ite (measurableSet_le measurable_snd (R.tm.measurable.comp measurable_fst))
      (R.bm.measurable.comp measurable_snd) measurable_const)
  have mms : Measurable ms := mean_meas (fun z => if z.2 ≤ R.T z.1 then R.S z.1 else 0)
    (Measurable.ite (measurableSet_le measurable_snd (R.tm.measurable.comp measurable_fst))
      (R.sm.measurable.comp measurable_fst) measurable_const)
  have i1 := mean_int mmb (C:=1) (fun y _ => mean_bound (fun x _ => by split <;> first | exact norm_unit (R.bb x) | norm_num))
  have i2 := mean_int mms (C:=1) (fun y _ => mean_bound (fun x _ => by split <;> first | exact norm_unit (R.sb y) | norm_num))
  rw [eq]
  calc
    _ = mean (fun y => mb y-ms y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc (s:=Icc (0:ℝ) 1)] with y hy
      dsimp only [mb,ms]
      rw [← mean_sub (ib y) (is' y)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc (s:=Icc (0:ℝ) 1),U.ae_ne (R.T y)] with x hx ne
      have iff := R.horizontal x hx y hy ne
      split_ifs <;> grind
    _ = mean mb - mean ms := mean_sub i1 i2
    _ = _ := by
      have em : mean ms = full R.S R.L := by
        have t := R.transpose (fun z => R.S z.2) (R.sm.measurable.comp measurable_snd) 1 (fun x _ y _ => norm_unit (R.sb y)) zero_le_one
        change mean ms = _ at t
        rw [t]
        exact congrArg mean (funext (fun x => mean_indicator R.S (R.lb x)))
      rw [em]
      exact congrArg (fun z => z-full R.S R.L) (congrArg mean (funext (fun y => mean_indicator R.B (R.tb y))))

theorem identity_at {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) :
    (1-h)*R.sellerTest h + h*R.buyerTest h =
    eta h * ((1-h)*edge R.B R.T h + h*area R.B R.T h) -
    eta (1-h) * ((1-(1-h))*edge R.S R.L (1-h) + (1-h)*area R.S R.L (1-h)) := by
  have bm := R.bm.measurable
  have sm := R.sm.measurable
  have lm := R.lm.measurable
  have tm := R.tm.measurable
  have s (y) := mul_unit (theta_unit hh) (R.tb y)
  have b (x) := mul_unit (eta_unit hh) (R.lb x)
  have one : mean (fun y => theta h*R.T y*(R.B (theta h*R.T y)-R.S (eta h*y))) =
      edge R.B R.T h - theta h * mean (fun y => R.T y*R.S (eta h*y)) := by
    unfold edge
    rw [← mean_mul,← mean_sub
      (mean_int (by fun_prop) (fun y _ => norm_unit (mul_unit (s y) (R.bb _))))
      (mean_int (by fun_prop) (fun y _ => norm_unit (mul_unit (theta_unit hh) (mul_unit (R.tb y) (R.sb _)))))]
    exact congrArg mean (funext (fun y => by ring))
  have two : mean (fun x => eta h*R.L x*(R.B (theta h*x)-R.S (eta h*R.L x))) =
      eta h * mean (fun x => R.L x*R.B (theta h*x)) - edge R.S R.L (1-h) := by
    unfold edge
    rw [theta_reflect,← mean_mul,← mean_sub
      (mean_int (by fun_prop) (fun x _ => norm_unit (mul_unit (eta_unit hh) (mul_unit (R.lb x) (R.bb _)))))
      (mean_int (by fun_prop) (fun x _ => norm_unit (mul_unit (b x) (R.sb _))))]
    exact congrArg mean (funext (fun x => by ring))
  rw [sellerTest,buyerTest,one,two,R.areaB,R.areaS,eta_reflect,theta_reflect]
  ring

private def profile (Q T : ℝ → ℝ) (h : ℝ) := eta h * ((1-h)*edge Q T h + h*area Q T h)

private theorem profile_meas {Q T : ℝ → ℝ} (qm : Measurable Q) (tm : Measurable T)
    (qb : ∀ x, Q x ∈ Icc 0 1) : Measurable (profile Q T) := by
  have th : Measurable theta := by unfold theta; fun_prop
  have et : Measurable eta := by unfold eta; fun_prop
  have pm := primitive_meas qm (fun x => norm_unit (qb x))
  have ed : Measurable (edge Q T) := mean_meas (fun z => theta z.1*T z.2*Q (theta z.1*T z.2)) (by fun_prop)
  have ar : Measurable (area Q T) := mean_meas (fun z => primitive Q (theta z.1*T z.2)) (by fun_prop)
  unfold profile
  fun_prop

private theorem profile_bound {Q T : ℝ → ℝ} (qb : ∀ x, Q x ∈ Icc 0 1)
    (tb : ∀ y, T y ∈ Icc 0 1) {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) : ‖profile Q T h‖ ≤ 2 := by
  have ed : ‖edge Q T h‖ ≤ 1 := mean_bound (fun y _ => norm_unit (mul_unit (mul_unit (theta_unit hh) (tb y)) (qb _)))
  have ar : ‖area Q T h‖ ≤ 1 := mean_bound (fun y _ => norm_unit (primitive_unit qb (mul_unit (theta_unit hh) (tb y))))
  have s : 1-h ∈ Icc (0:ℝ) 1 := ⟨by linarith [hh.2],by linarith [hh.1]⟩
  unfold profile
  rw [norm_mul]
  calc
    _ ≤ 1 * (‖(1-h)*edge Q T h‖+‖h*area Q T h‖) := mul_le_mul (norm_unit (eta_unit hh)) (norm_add_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ 2 := by
      rw [one_mul,norm_mul,norm_mul]
      nlinarith [mul_le_mul (norm_unit s) ed (norm_nonneg _) zero_le_one,
        mul_le_mul (norm_unit hh) ar (norm_nonneg _) zero_le_one]

include R in
theorem guarantee : I.FB ≤ Real.exp 1 * I.roProfit := by
  let buy := profile R.B R.T
  let sell (h : ℝ) := profile R.S R.L (1-h)
  have buyI : Integrable buy U := mean_int (profile_meas R.bm.measurable R.tm.measurable R.bb) (fun h hh => profile_bound R.bb R.tb hh)
  have sellI : Integrable sell U :=
    mean_int ((profile_meas R.sm.measurable R.lm.measurable R.sb).comp (measurable_const.sub measurable_id))
      (fun h hh => profile_bound R.sb R.lb ⟨by linarith [hh.2],by linarith [hh.1]⟩)
  have bval : mean buy = Real.exp (-1)*full R.B R.T :=
    scale_mean _ _ R.bm.measurable R.tm.measurable R.bb R.tb R.bm.countable_not_continuousAt
  have sval : mean sell = Real.exp (-1)*full R.S R.L :=
    (mean_reflect _).trans (scale_mean _ _ R.sm.measurable R.lm.measurable R.sb R.lb R.sm.countable_not_continuousAt)
  let A (h : ℝ) := (1-h)*I.sellerProfit
  let D (h : ℝ) := h*I.buyerProfit
  have unit_int : Integrable (fun h : ℝ => h) U := mean_int measurable_id (fun _ hh => norm_unit hh)
  have ia : Integrable A U := ((integrable_const (1:ℝ)).sub unit_int).mul_const _
  have id' : Integrable D U := unit_int.mul_const _
  have p := mean_ge (f:=fun h => buy h-sell h) (g:=fun h => A h+D h) (buyI.sub sellI) (ia.add id') (fun h hh => by
    change profile _ _ h-profile _ _ (1-h) ≤ _
    rw [show profile R.B R.T h-profile R.S R.L (1-h) = (1-h)*R.sellerTest h + h*R.buyerTest h from (R.identity_at hh).symm]
    exact add_le_add (mul_le_mul_of_nonneg_left (R.seller_test_le hh) (sub_nonneg.mpr hh.2))
      (mul_le_mul_of_nonneg_left (R.buyer_test_le hh) hh.1))
  rw [mean_sub buyI sellI,mean_add ia id',bval,sval,← mul_sub,← R.fb_eq] at p
  have a : mean A = (1/2)*I.sellerProfit := by
    change (∫ h, (1-h)*I.sellerProfit ∂U) = _
    rw [integral_mul_const]
    exact congrArg (·*I.sellerProfit) mean_one_sub
  have d : mean D = (1/2)*I.buyerProfit := by
    change (∫ h, h*I.buyerProfit ∂U) = _
    rw [integral_mul_const]
    exact congrArg (·*I.buyerProfit) mean_identity
  rw [a,d,Real.exp_neg] at p
  have mul := mul_le_mul_of_nonneg_left p (Real.exp_pos 1).le
  rw [← mul_assoc,mul_inv_cancel₀ (Real.exp_pos 1).ne',one_mul] at mul
  unfold BTInstance.roProfit
  linarith only [mul]

end Region
end StratifyMarkets.DoubleAuction.Rank

namespace StratifyMarkets.DoubleAuction
theorem randomOffererBenchmark (I : BTInstance) : I.FB ≤ Real.exp 1 * I.roProfit := by
  obtain ⟨R⟩ := Rank.region I
  exact R.guarantee
end StratifyMarkets.DoubleAuction
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_theorem_2_2
section
open StratifyMarkets.DoubleAuction

theorem solution (I : BTInstance) : I.FB ≤ Real.exp 1 * I.roProfit :=
  randomOffererBenchmark I
end
