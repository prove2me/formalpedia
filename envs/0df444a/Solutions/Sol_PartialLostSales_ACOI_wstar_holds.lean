-- Prove2me | solution 1 for PartialLostSales.ACOI.wstar_holds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:22:38.727546+00:00
-- url     : https://prove2.me/submissions/4bf147bf-bcee-4d1a-af87-6cf428845599

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model
import Theorems.Thm_ProbabilityMeasureSpace_secondCountableTopology
import Theorems.Thm_ProbabilityMeasureSpace_borelSpace

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace PLSWStarAux
open PartialLostSales.ACOI

/-- `ν ↦ ∫⁻ C dν` is lower semicontinuous for a continuous `C : ℝ → ℝ≥0`. -/
lemma lsc_lintegral (C : ℝ → ℝ≥0) (hC : Continuous C) :
    LowerSemicontinuous (fun ν : ProbabilityMeasure ℝ => ∫⁻ y, (C y : ℝ≥0∞) ∂(ν : Measure ℝ)) := by
  let f : ℕ → ℝ →ᵇ ℝ≥0 := fun n => BoundedContinuousFunction.mkOfBound
    ⟨fun y => min (C y) n, hC.min continuous_const⟩ n (fun x y => by
      simp only [ContinuousMap.coe_mk, NNReal.dist_eq]
      have h1 : ((min (C x) n : ℝ≥0) : ℝ) ≤ n := by exact_mod_cast min_le_right _ _
      have h2 : ((min (C y) n : ℝ≥0) : ℝ) ≤ n := by exact_mod_cast min_le_right _ _
      have h3 : (0:ℝ) ≤ ((min (C x) n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have h4 : (0:ℝ) ≤ ((min (C y) n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      rw [abs_le]; constructor <;> linarith)
  have e : (fun ν : ProbabilityMeasure ℝ => ∫⁻ y, (C y : ℝ≥0∞) ∂(ν : Measure ℝ)) =
      fun ν : ProbabilityMeasure ℝ => ⨆ n : ℕ, ∫⁻ y, ((f n y : ℝ≥0) : ℝ≥0∞) ∂(ν : Measure ℝ) := by
    funext ν
    rw [← lintegral_iSup]
    · congr 1
      funext y
      apply le_antisymm
      · refine le_iSup_of_le ⌈(C y : ℝ)⌉₊ ?_
        simp only [f, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
        rw [min_eq_left]
        have := Nat.le_ceil (C y : ℝ)
        exact_mod_cast this
      · exact iSup_le fun n => by
          simp only [f, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
          exact_mod_cast min_le_left _ _
    · intro n
      exact (ENNReal.continuous_coe.comp (f n).continuous).measurable
    · intro n m hnm y
      simp only [f, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
      exact_mod_cast min_le_min_left _ (by exact_mod_cast hnm)
  rw [e]
  exact lowerSemicontinuous_iSup fun n =>
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (f n)).lowerSemicontinuous

lemma continuous_add_act (P : Params) :
    Continuous (fun q : ℝ≥0 × Act P => (q.1 : ℝ) + (q.2 : ℝ)) := by fun_prop

/-- The law of `x + a` for `x ∼ z`. -/
noncomputable def Lam (P : Params) (p : Bel P × Act P) : ProbabilityMeasure ℝ :=
  ((p.1.1).prod (diracProba p.2)).map (continuous_add_act P).measurable.aemeasurable

lemma continuous_Lam (P : Params) : Continuous (Lam P) := by
  unfold Lam
  refine (ProbabilityMeasure.continuous_map (continuous_add_act P)).comp ?_
  exact ProbabilityMeasure.continuous_prod.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_diracProba.comp continuous_snd))

lemma lintegral_Lam (P : Params) {h : ℝ → ℝ≥0∞} (hh : Measurable h) (p : Bel P × Act P) :
    ∫⁻ y, h y ∂(Lam P p : Measure ℝ) = ∫⁻ x, h ((x : ℝ) + (p.2 : ℝ)) ∂(p.1.1 : Measure ℝ≥0) := by
  simp only [Lam, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod]
  rw [lintegral_map hh (continuous_add_act P).measurable]
  show ∫⁻ q, h ((q.1 : ℝ) + (q.2 : ℝ)) ∂((p.1.1 : Measure ℝ≥0).prod (Measure.dirac p.2)) = _
  rw [Measure.prod_dirac, lintegral_map (f := fun q : ℝ≥0 × Act P => h ((q.1 : ℝ) + (q.2 : ℝ)))
    (hh.comp (continuous_add_act P).measurable) measurable_prodMk_right]

lemma integral_Lam (P : Params) (h : ℝ →ᵇ ℝ) (p : Bel P × Act P) :
    ∫ y, h y ∂(Lam P p : Measure ℝ) = ∫ x, h ((x : ℝ) + (p.2 : ℝ)) ∂(p.1.1 : Measure ℝ≥0) := by
  simp only [Lam, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod]
  rw [integral_map (continuous_add_act P).measurable.aemeasurable
    h.continuous.aestronglyMeasurable]
  show ∫ q, h ((q.1 : ℝ) + (q.2 : ℝ)) ∂((p.1.1 : Measure ℝ≥0).prod (Measure.dirac p.2)) = _
  rw [Measure.prod_dirac, integral_map (f := fun q : ℝ≥0 × Act P => h ((q.1 : ℝ) + (q.2 : ℝ)))
    measurable_prodMk_right.aemeasurable
    (h.continuous.comp (continuous_add_act P)).aestronglyMeasurable]

/-- The lower semicontinuity of `c̄`. -/
lemma lsc_cbar (P : Params) (hP : Standing P) :
    LowerSemicontinuous (fun p : Bel P × Act P => cbar P p.1 p.2) := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  let φ : ℝ → ℝ → ℝ := fun y s => P.hplus * max (y - s) 0 + P.hminus * max (s - y) 0
  have hφnn : ∀ y s, 0 ≤ φ y s := fun y s => by positivity
  have hφb : ∀ y s, φ y s ≤ (P.hplus + P.hminus) * (|y| + |s|) := by
    intro y s
    have h1 : max (y - s) 0 ≤ |y| + |s| :=
      max_le (by linarith [le_abs_self y, neg_abs_le s]) (by positivity)
    have h2 : max (s - y) 0 ≤ |y| + |s| :=
      max_le (by linarith [le_abs_self s, neg_abs_le y]) (by positivity)
    simp only [φ]
    nlinarith [mul_le_mul_of_nonneg_left h1 hhp.le, mul_le_mul_of_nonneg_left h2 hhm.le]
  have hφL : ∀ y y' s, |φ y s - φ y' s| ≤ (P.hplus + P.hminus) * |y - y'| := by
    intro y y' s
    have h1 : |max (y - s) 0 - max (y' - s) 0| ≤ |y - y'| := by
      have := abs_max_sub_max_le_abs (y - s) (y' - s) 0
      simpa using this
    have h2 : |max (s - y) 0 - max (s - y') 0| ≤ |y - y'| := by
      have := abs_max_sub_max_le_abs (s - y) (s - y') 0
      rw [show s - y - (s - y') = -(y - y') by ring, abs_neg] at this
      exact this
    simp only [φ]
    calc |P.hplus * max (y - s) 0 + P.hminus * max (s - y) 0 -
          (P.hplus * max (y' - s) 0 + P.hminus * max (s - y') 0)|
        = |P.hplus * (max (y - s) 0 - max (y' - s) 0) +
            P.hminus * (max (s - y) 0 - max (s - y') 0)| := by ring_nf
      _ ≤ |P.hplus * (max (y - s) 0 - max (y' - s) 0)| +
            |P.hminus * (max (s - y) 0 - max (s - y') 0)| := abs_add_le _ _
      _ = P.hplus * |max (y - s) 0 - max (y' - s) 0| +
            P.hminus * |max (s - y) 0 - max (s - y') 0| := by
          rw [abs_mul, abs_mul, abs_of_pos hhp, abs_of_pos hhm]
      _ ≤ P.hplus * |y - y'| + P.hminus * |y - y'| := by gcongr
      _ = _ := by ring
  have hφm : ∀ y, Measurable (φ y) := fun y => by simp only [φ]; fun_prop
  have hφi : ∀ y, Integrable (φ y) P.demand := by
    intro y
    refine Integrable.mono' (((integrable_const |y|).add hint.abs).const_mul
      (P.hplus + P.hminus)) (hφm y).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφnn y s)]
    exact hφb y s
  let Cr : ℝ → ℝ := fun y => ∫ s, φ y s ∂P.demand
  have hCr : Continuous Cr := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨P.hplus + P.hminus, by positivity⟩)
      fun y y' => ?_).continuous
    simp only [Real.dist_eq, Cr]
    rw [← integral_sub (hφi y) (hφi y')]
    calc |∫ s, (φ y s - φ y' s) ∂P.demand| ≤ ∫ s, |φ y s - φ y' s| ∂P.demand :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _s, (P.hplus + P.hminus) * |y - y'| ∂P.demand :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
            (ae_of_all _ fun s => hφL y y' s)
      _ = _ := by simp; left; rfl
  let C : ℝ → ℝ≥0 := fun y => Real.toNNReal (Cr y)
  have hC : Continuous C := continuous_real_toNNReal.comp hCr
  have hcb : ∀ p : Bel P × Act P, cbar P p.1 p.2 = ∫⁻ y, (C y : ℝ≥0∞) ∂(Lam P p : Measure ℝ) := by
    intro p
    rw [lintegral_Lam P (h := fun y => (C y : ℝ≥0∞)) (ENNReal.continuous_coe.comp hC).measurable p]
    unfold cbar c
    congr 1
    funext x
    show _ = ENNReal.ofReal (Cr _)
    rw [ofReal_integral_eq_lintegral_ofReal (hφi _) (ae_of_all _ fun s => hφnn _ s)]
    congr 1
    funext s
    simp only [φ]
    congr 2
    ring_nf
  have : (fun p : Bel P × Act P => cbar P p.1 p.2) =
      (fun ν : ProbabilityMeasure ℝ => ∫⁻ y, (C y : ℝ≥0∞) ∂(ν : Measure ℝ)) ∘ Lam P := by
    funext p; exact hcb p
  rw [this]
  exact (lsc_lintegral C hC).comp (continuous_Lam P)

/-- The kernel function `G_g(y) = E[g((y - D)⁺); D < y]`. -/
noncomputable def Gfun (P : Params) (g : ℝ≥0 →ᵇ ℝ) (y : ℝ) : ℝ :=
  ∫ s, (Iio y).indicator (fun s => g (Real.toNNReal (y - s))) s ∂P.demand

lemma Gfun_le (P : Params) (hP : Standing P) (g : ℝ≥0 →ᵇ ℝ) (y : ℝ) : |Gfun P g y| ≤ ‖g‖ := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  unfold Gfun
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖g‖) (ae_of_all _ fun s => ?_)).trans
    (by simp)
  by_cases hs : s ∈ Iio y
  · rw [indicator_of_mem hs]; exact g.norm_coe_le_norm _
  · rw [indicator_of_notMem hs, norm_zero]; exact norm_nonneg _

lemma continuous_Gfun (P : Params) (hP : Standing P) (g : ℝ≥0 →ᵇ ℝ) :
    Continuous (Gfun P g) := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  rw [continuous_iff_continuousAt]
  intro y0
  have hmeas : ∀ y, AEStronglyMeasurable
      (fun s => (Iio y).indicator (fun s => g (Real.toNNReal (y - s))) s) P.demand := by
    intro y
    refine (Measurable.indicator ?_ measurableSet_Iio).aestronglyMeasurable
    exact g.continuous.measurable.comp (by fun_prop)
  refine continuousAt_of_dominated (bound := fun _ => ‖g‖) (Eventually.of_forall hmeas)
    (Eventually.of_forall fun y => ae_of_all _ fun s => ?_) (integrable_const _) ?_
  · by_cases hs : s ∈ Iio y
    · rw [indicator_of_mem hs]; exact g.norm_coe_le_norm _
    · rw [indicator_of_notMem hs, norm_zero]; exact norm_nonneg _
  · have h0 : P.demand {y0} = 0 := hac (Real.volume_singleton)
    have : ∀ᵐ s ∂P.demand, s ≠ y0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [this] with s hs
    rcases lt_or_gt_of_ne hs with h | h
    · -- s < y0 : eventually s < y
      have hev : ∀ᶠ y in 𝓝 y0, (Iio y).indicator (fun s => g (Real.toNNReal (y - s))) s =
          g (Real.toNNReal (y - s)) := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        exact indicator_of_mem (show s ∈ Iio y from hy) _
      refine ContinuousAt.congr ?_ (EventuallyEq.symm hev)
      exact (g.continuous.comp (continuous_real_toNNReal.comp
        (continuous_id.sub continuous_const))).continuousAt
    · have hev : ∀ᶠ y in 𝓝 y0, (Iio y).indicator (fun s => g (Real.toNNReal (y - s))) s = 0 := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact indicator_of_notMem (show s ∉ Iio y from fun h2 => lt_asymm (show s < y from h2) (show y < s from hy)) _
      exact ContinuousAt.congr continuousAt_const (EventuallyEq.symm hev)

/-- `G_g` as a bounded continuous function. -/
noncomputable def Gbcf (P : Params) (hP : Standing P) (g : ℝ≥0 →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨Gfun P g, continuous_Gfun P hP g⟩ (2 * ‖g‖)
    (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := Gfun_le P hP g x
      have h2 := Gfun_le P hP g y
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])

lemma integral_restrict_nextLaw (P : Params) (hP : Standing P) (g : ℝ≥0 →ᵇ ℝ)
    (p : Bel P × Act P) :
    ∫ x, g x ∂((nextLaw P p.1.1 p.2).restrict (Ioi 0)) =
      ∫ y, Gbcf P hP g y ∂(Lam P p : Measure ℝ) := by
  have hP' := hP
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP'
  rw [integral_Lam]
  rw [← integral_indicator measurableSet_Ioi]
  have hT : Measurable (fun q : ℝ≥0 × ℝ => Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2)) := by
    fun_prop
  have hgi : Measurable ((Ioi (0:ℝ≥0)).indicator (fun x => g x)) :=
    g.continuous.measurable.indicator measurableSet_Ioi
  unfold nextLaw
  rw [integral_map hT.aemeasurable hgi.aestronglyMeasurable]
  rw [integral_prod]
  · congr 1
    funext x
    simp only [Gbcf, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, Gfun]
    congr 1
    funext s
    by_cases hs : s < (x : ℝ) + (p.2 : ℝ)
    · rw [indicator_of_mem (show s ∈ Iio ((x : ℝ) + (p.2 : ℝ)) from hs),
        indicator_of_mem (show Real.toNNReal ((x : ℝ) + (p.2 : ℝ) - s) ∈ Ioi 0 from by
          simp only [mem_Ioi, Real.toNNReal_pos]; linarith)]
    · rw [indicator_of_notMem (show s ∉ Iio ((x : ℝ) + (p.2 : ℝ)) from hs),
        indicator_of_notMem (show Real.toNNReal ((x : ℝ) + (p.2 : ℝ) - s) ∉ Ioi 0 from by
          simp only [mem_Ioi, Real.toNNReal_pos, not_lt]; linarith [not_lt.1 hs])]
  · refine Integrable.mono' (integrable_const ‖g‖) (hgi.comp hT).aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    show ‖(Ioi (0:ℝ≥0)).indicator (fun x => g x) (Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2))‖ ≤ ‖g‖
    by_cases hq : Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2) ∈ Ioi 0
    · rw [indicator_of_mem hq]; exact g.norm_coe_le_norm _
    · rw [indicator_of_notMem hq, norm_zero]; exact norm_nonneg _

lemma isProb_nextLaw (P : Params) (hP : Standing P) (z : ProbabilityMeasure ℝ≥0) (a : ℝ) :
    IsProbabilityMeasure (nextLaw P z a) := by
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP
  unfold nextLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma continuous_mg (P : Params) (hP : Standing P) (g : ℝ≥0 →ᵇ ℝ) :
    Continuous (fun p : Bel P × Act P => ∫ x, g x ∂((nextLaw P p.1.1 p.2).restrict (Ioi 0))) := by
  simp_rw [integral_restrict_nextLaw P hP g]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _).comp (continuous_Lam P)

lemma R1_toReal_eq (P : Params) (hP : Standing P) (p : Bel P × Act P) :
    (R1 P p.1.1 p.2).toReal =
      ∫ x, (BoundedContinuousFunction.const ℝ≥0 (1:ℝ)) x ∂((nextLaw P p.1.1 p.2).restrict (Ioi 0)) := by
  haveI := isProb_nextLaw P hP p.1.1 p.2
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one, R1]
  rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]

lemma continuous_r (P : Params) (hP : Standing P) :
    Continuous (fun p : Bel P × Act P => (R1 P p.1.1 p.2).toReal) := by
  simp_rw [R1_toReal_eq P hP]
  exact continuous_mg P hP _

lemma integral_post (P : Params) (hP : Standing P) (g : ℝ≥0 →ᵇ ℝ) (p : Bel P × Act P)
    (hr : R1 P p.1.1 p.2 ≠ 0) :
    ∫ x, g x ∂((post P p.1.1 p.2 : ProbabilityMeasure ℝ≥0) : Measure ℝ≥0) =
      ((R1 P p.1.1 p.2).toReal)⁻¹ * ∫ x, g x ∂((nextLaw P p.1.1 p.2).restrict (Ioi 0)) := by
  haveI := isProb_nextLaw P hP p.1.1 p.2
  have hc : nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤ :=
    ⟨hr, measure_ne_top _ _⟩
  have e : post P p.1.1 p.2 = ⟨ProbabilityTheory.cond (nextLaw P p.1.1 p.2) (Ioi 0),
      ProbabilityTheory.cond_isProbabilityMeasure_of_finite hc.1 hc.2⟩ := dif_pos hc
  rw [e]
  show ∫ x, g x ∂((nextLaw P p.1.1 p.2 (Ioi 0))⁻¹ • (nextLaw P p.1.1 p.2).restrict (Ioi 0)) = _
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

lemma post_secondMoment (P : Params) (hP : Standing P) (p : Bel P × Act P)
    (hr : R1 P p.1.1 p.2 ≠ 0) :
    secondMoment ((post P p.1.1 p.2 : ProbabilityMeasure ℝ≥0) : Measure ℝ≥0) < ⊤ := by
  have hP' := hP
  obtain ⟨hK, hhp, hhm, hprob, hac, hint, hmean, hvar, hneg⟩ := hP'
  haveI := isProb_nextLaw P hP p.1.1 p.2
  have hc : nextLaw P p.1.1 p.2 (Ioi 0) ≠ 0 ∧ nextLaw P p.1.1 p.2 (Ioi 0) ≠ ⊤ :=
    ⟨hr, measure_ne_top _ _⟩
  have e : post P p.1.1 p.2 = ⟨ProbabilityTheory.cond (nextLaw P p.1.1 p.2) (Ioi 0),
      ProbabilityTheory.cond_isProbabilityMeasure_of_finite hc.1 hc.2⟩ := dif_pos hc
  rw [e]
  unfold secondMoment
  show ∫⁻ x, (x : ℝ≥0∞) ^ 2 ∂((nextLaw P p.1.1 p.2 (Ioi 0))⁻¹ •
    (nextLaw P p.1.1 p.2).restrict (Ioi 0)) < ⊤
  rw [lintegral_smul_measure]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hr)) ?_
  have hT : Measurable (fun q : ℝ≥0 × ℝ => Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2)) := by
    fun_prop
  set K' : ℝ≥0 := Real.toNNReal P.K
  have hae : ∀ᵐ q ∂((p.1.1 : Measure ℝ≥0).prod P.demand), 0 ≤ q.2 := by
    rw [ae_iff]
    have : {q : ℝ≥0 × ℝ | ¬ 0 ≤ q.2} = univ ×ˢ Iio 0 := by ext q; simp
    rw [this, Measure.prod_prod, hneg, mul_zero]
  calc ∫⁻ x, (x : ℝ≥0∞) ^ 2 ∂((nextLaw P p.1.1 p.2).restrict (Ioi 0))
      ≤ ∫⁻ x, (x : ℝ≥0∞) ^ 2 ∂(nextLaw P p.1.1 p.2) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ q, ((Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2) : ℝ≥0) : ℝ≥0∞) ^ 2
          ∂((p.1.1 : Measure ℝ≥0).prod P.demand) := by
        unfold nextLaw
        rw [lintegral_map (by fun_prop) hT]
    _ ≤ ∫⁻ q, ((2 * (q.1 ^ 2 + K' ^ 2) : ℝ≥0) : ℝ≥0∞)
          ∂((p.1.1 : Measure ℝ≥0).prod P.demand) := by
        refine lintegral_mono_ae (hae.mono fun q hq => ?_)
        have h1 : Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2) ≤ q.1 + K' := by
          rw [Real.toNNReal_le_iff_le_coe]
          have := (p.2).2.2
          have : P.K ≤ (K' : ℝ) := Real.le_coe_toNNReal _
          push_cast
          linarith
        have h2 : (Real.toNNReal ((q.1 : ℝ) + (p.2 : ℝ) - q.2)) ^ 2 ≤ 2 * (q.1 ^ 2 + K' ^ 2) :=
          (pow_le_pow_left₀ (zero_le) h1 2).trans add_sq_le
        rw [← ENNReal.coe_pow]
        exact_mod_cast h2
    _ = ∫⁻ x, ((2 * (x ^ 2 + K' ^ 2) : ℝ≥0) : ℝ≥0∞) ∂(p.1.1 : Measure ℝ≥0) := by
        rw [← lintegral_map (f := fun x : ℝ≥0 => ((2 * (x ^ 2 + K' ^ 2) : ℝ≥0) : ℝ≥0∞))
          (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    _ < ⊤ := by
        have h2 := p.1.2
        unfold secondMoment at h2
        push_cast
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_right _ measurable_const]
        refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2 ⟨h2, ?_⟩)
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (by simp) (by simp)

end PLSWStarAux

open PartialLostSales.ACOI PLSWStarAux in
theorem solution (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    AssumptionWStar M := by
  haveI : SecondCountableTopology (ProbabilityMeasure ℝ≥0) :=
    ProbabilityMeasureSpace.secondCountableTopology
  haveI : BorelSpace (ProbabilityMeasure ℝ≥0) := ProbabilityMeasureSpace.borelSpace
  haveI : BorelSpace (Bel P) := Subtype.borelSpace _
  refine ⟨?_, ?_⟩
  · intro K _ hKc l
    have hcl : IsClosed ((fun p : Bel P × Act P => cbar P p.1 p.2) ⁻¹' Iic (l : ℝ≥0∞)) :=
      (lsc_cbar P hP).isClosed_preimage _
    have e : {p : Bel P × Act P | p.1 ∈ K ∧ M.cost p.1 p.2 ≤ (l : ℝ≥0∞)} =
        (K ×ˢ univ) ∩ ((fun p : Bel P × Act P => cbar P p.1 p.2) ⁻¹' Iic (l : ℝ≥0∞)) := by
      ext p
      simp [hM.2.1]
    rw [e]
    exact (hKc.prod isCompact_univ).inter_right hcl
  · intro f
    let r : Bel P × Act P → ℝ := fun p => (R1 P p.1.1 p.2).toReal
    let b : Bel P × Act P → Bel P := fun p => toBel P (post P p.1.1 p.2)
    have hr : Continuous r := continuous_r P hP
    have hform : ∀ p : Bel P × Act P, ∫ y, f y ∂(M.q p) =
        (1 - r p) * f (δ0 P) + r p * f (b p) := by
      intro p
      haveI := isProb_nextLaw P hP p.1.1 p.2
      have hsum : R0 P p.1.1 p.2 + R1 P p.1.1 p.2 = 1 := by
        unfold R0 R1
        rw [← measure_union (by simp) measurableSet_Ioi]
        have : ({0} ∪ Ioi 0 : Set ℝ≥0) = univ := by
          ext x; simp only [mem_union, mem_singleton_iff, mem_Ioi, mem_univ, iff_true]
          exact (eq_or_ne x 0).imp id pos_iff_ne_zero.2
        rw [this, measure_univ]
      have hR0 : (R0 P p.1.1 p.2).toReal = 1 - r p := by
        have h1 : R1 P p.1.1 p.2 ≠ ⊤ := measure_ne_top _ _
        have h0 : R0 P p.1.1 p.2 ≠ ⊤ := measure_ne_top _ _
        have := congrArg ENNReal.toReal hsum
        rw [ENNReal.toReal_add h0 h1, ENNReal.toReal_one] at this
        simp only [r]; linarith
      have hq : M.q p = qBel P p.1 p.2 := hM.2.2 p.1 p.2
      rw [hq]
      unfold qBel
      haveI : IsFiniteMeasure (R0 P p.1.1 p.2 • Measure.dirac (δ0 P)) :=
        Measure.smul_finite _ (measure_ne_top _ _)
      haveI : IsFiniteMeasure (R1 P p.1.1 p.2 • Measure.dirac (toBel P (post P p.1.1 p.2))) :=
        Measure.smul_finite _ (measure_ne_top _ _)
      rw [integral_add_measure (f.integrable _) (f.integrable _), integral_smul_measure,
        integral_smul_measure, integral_dirac, integral_dirac, hR0]
      rfl
    have e : (fun p : Bel P × Act P => ∫ y, f y ∂(M.q p)) =
        fun p => (1 - r p) * f (δ0 P) + r p * f (b p) := funext hform
    rw [e]
    refine ((continuous_const.sub hr).mul continuous_const).add ?_
    rw [continuous_iff_continuousAt]
    intro p0
    by_cases h0 : R1 P p0.1.1 p0.2 = 0
    · have hr0 : r p0 = 0 := by simp [r, h0]
      show Tendsto (fun p => r p * f (b p)) (𝓝 p0) (𝓝 (r p0 * f (b p0)))
      rw [hr0, zero_mul]
      refine squeeze_zero_norm (a := fun p => r p * ‖f‖) (fun p => ?_) ?_
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) ENNReal.toReal_nonneg
      · have := (hr.tendsto p0).mul_const ‖f‖
        rwa [hr0, zero_mul] at this
    · haveI := isProb_nextLaw P hP p0.1.1 p0.2
      have hrpos : 0 < r p0 := ENNReal.toReal_pos h0 (measure_ne_top _ _)
      have hev : ∀ᶠ p in 𝓝 p0, 0 < r p := hr.continuousAt.eventually (Ioi_mem_nhds hrpos)
      have hpost : Tendsto (fun p => post P p.1.1 p.2) (𝓝 p0) (𝓝 (post P p0.1.1 p0.2)) := by
        rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
        intro g
        have hlim : Tendsto (fun p => (r p)⁻¹ *
            ∫ x, g x ∂((nextLaw P p.1.1 p.2).restrict (Ioi 0))) (𝓝 p0)
            (𝓝 ((r p0)⁻¹ * ∫ x, g x ∂((nextLaw P p0.1.1 p0.2).restrict (Ioi 0)))) :=
          ((hr.tendsto p0).inv₀ hrpos.ne').mul ((continuous_mg P hP g).tendsto p0)
        rw [integral_post P hP g p0 h0]
        refine hlim.congr' ?_
        filter_upwards [hev] with p hp
        have hp' : R1 P p.1.1 p.2 ≠ 0 := fun h => by simp [r, h] at hp
        rw [integral_post P hP g p hp']
      have hb : Tendsto b (𝓝 p0) (𝓝 (b p0)) := by
        rw [tendsto_subtype_rng]
        have hval : ∀ p : Bel P × Act P, R1 P p.1.1 p.2 ≠ 0 → (b p).1 = post P p.1.1 p.2 := by
          intro p hp
          show (toBel P (post P p.1.1 p.2)).1 = _
          rw [toBel, dif_pos (post_secondMoment P hP p hp)]
        rw [hval p0 h0]
        refine hpost.congr' ?_
        filter_upwards [hev] with p hp
        have hp' : R1 P p.1.1 p.2 ≠ 0 := fun h => by simp [r, h] at hp
        exact (hval p hp').symm
      exact (hr.tendsto p0).mul ((f.continuous.tendsto _).comp hb)


