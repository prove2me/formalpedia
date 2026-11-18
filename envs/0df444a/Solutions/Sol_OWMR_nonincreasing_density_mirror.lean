-- Prove2me | solution 1 for OWMR.nonincreasing_density_mirror
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:48:10.981479+00:00
-- url     : https://prove2.me/submissions/28e39d18-8bf2-4ebe-9592-58a48103f40c

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Slope

/-!
Lemma D.2 (Nonincreasing-Density Mirror Bound). If `Y` has a possible atom at zero and a
nonincreasing density on `(0, w)`, then `y ↦ ℙ(0 ≤ Y ≤ y)` is concave on `[0, w]` (its slopes over
adjacent intervals are bounded below and above by the density at the common endpoint). At the
target `m = w (1 - σ)`, `σ = √(p/(p+h))`, the two hinge parts equal integrals of the distribution
function (Tonelli), the chords of the concave distribution function through `m` and `w` bound them,
and `h (w - m)² = p (2 w m - m²)` balances the two chord integrals, giving
`𝔼[p (m - Y)⁺ + h (Y - m)⁺] ≤ p m = p (1 - σ) w`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace NDM

/-- Tonelli for the lower hinge: `∫_A (m - x)⁺ dμ = ∫_{y ≤ m} μ(A ∩ (-∞, y]) dy`. -/
lemma tonelli_left (μ : Measure ℝ) [SFinite μ] (m : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∫⁻ x in A, ENNReal.ofReal (m - x) ∂μ = ∫⁻ y in Iic m, μ (A ∩ Iic y) := by
  have h1 : ∀ x, ENNReal.ofReal (m - x) = ∫⁻ y, (Icc x m).indicator 1 y := by
    intro x
    rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun x y : ℝ => (Icc x m).indicator (1 : ℝ → ℝ≥0∞) y) := by
    have : (Function.uncurry fun x y : ℝ => (Icc x m).indicator (1 : ℝ → ℝ≥0∞) y)
        = {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ m}.indicator 1 := by
      ext ⟨x, y⟩
      simp [Set.indicator, Set.mem_Icc]
    rw [this]
    exact measurable_one.indicator
      ((measurableSet_le measurable_fst measurable_snd).inter (measurableSet_le measurable_snd measurable_const))
  rw [lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ≤ m
  · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy)]
    rw [← lintegral_indicator_one (hA.inter measurableSet_Iic), ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A <;> by_cases hxy : x ≤ y <;> simp [Set.indicator, hx, hxy, hy, Set.mem_Icc]
  · rw [Set.indicator_of_notMem (by simpa using hy)]
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun x => ?_)
    simp [Set.indicator, Set.mem_Icc, hy]

/-- Tonelli for the upper hinge: `∫_A (x - m)⁺ dμ = ∫_{y ≥ m} μ(A ∩ (y, ∞)) dy`. -/
lemma tonelli_right (μ : Measure ℝ) [SFinite μ] (m : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∫⁻ x in A, ENNReal.ofReal (x - m) ∂μ = ∫⁻ y in Ici m, μ (A ∩ Ioi y) := by
  have h1 : ∀ x, ENNReal.ofReal (x - m) = ∫⁻ y, (Ico m x).indicator 1 y := by
    intro x
    rw [lintegral_indicator_one measurableSet_Ico, Real.volume_Ico]
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun x y : ℝ => (Ico m x).indicator (1 : ℝ → ℝ≥0∞) y) := by
    have : (Function.uncurry fun x y : ℝ => (Ico m x).indicator (1 : ℝ → ℝ≥0∞) y)
        = {p : ℝ × ℝ | m ≤ p.2 ∧ p.2 < p.1}.indicator 1 := by
      ext ⟨x, y⟩
      simp [Set.indicator, Set.mem_Ico]
    rw [this]
    exact measurable_one.indicator
      ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_lt measurable_snd measurable_fst))
  rw [lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_indicator measurableSet_Ici]
  refine lintegral_congr fun y => ?_
  by_cases hy : m ≤ y
  · rw [Set.indicator_of_mem (Set.mem_Ici.2 hy)]
    rw [← lintegral_indicator_one (hA.inter measurableSet_Ioi), ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A <;> by_cases hxy : y < x <;> simp [Set.indicator, hx, hxy, hy, Set.mem_Ico]
  · rw [Set.indicator_of_notMem (by simpa using hy)]
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun x => ?_)
    simp [Set.indicator, Set.mem_Ico, hy]


lemma intOn_fin (μ : Measure ℝ) [IsFiniteMeasure μ] {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    IntegrableOn φ (Ico a b) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn
  exact Measure.integrableOn_of_bounded (M := C) (measure_ne_top μ _) hφ.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hC x (Ico_subset_Icc_self hx))

/-- The bound for a law carried by `[0, w)` whose distribution function is concave on `[0, w]`. -/
lemma core (μ : Measure ℝ) [IsProbabilityMeasure μ] (h p w : ℝ) (hh : 0 < h) (hp : 0 < p)
    (hw0 : 0 < w) (hsupp : μ (Ico 0 w) = 1)
    (hconc : ConcaveOn ℝ (Icc 0 w) (fun y => (μ (Icc 0 y)).toReal)) :
    ∫ y, (p * max (w * (1 - Real.sqrt (p / (p + h))) - y) 0
        + h * max (y - w * (1 - Real.sqrt (p / (p + h)))) 0) ∂μ
      ≤ p * (1 - Real.sqrt (p / (p + h))) * w := by
  have hae : ∀ᵐ x ∂μ, x ∈ Ico (0 : ℝ) w := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff measurableSet_Ico).2 hsupp
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  -- the center parameters
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (p / (p + h)) := ⟨_, rfl⟩
  rw [← hσ]
  have hpph : 0 < p / (p + h) := div_pos hp (by linarith)
  have hσ0 : 0 < σ := by rw [hσ]; exact Real.sqrt_pos.2 hpph
  have hσsq : σ ^ 2 = p / (p + h) := by rw [hσ]; exact Real.sq_sqrt hpph.le
  have hσ1 : σ < 1 := by
    have : p / (p + h) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = w * (1 - σ) := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 < m := by rw [hm]; exact mul_pos hw0 (by linarith)
  have hmw : m < w := by rw [hm]; nlinarith
  -- `W y = μ[0, y]`
  set W : ℝ → ℝ := fun y => (μ (Icc 0 y)).toReal with hWdef
  set M : ℝ := 1 with hM
  have hWmono : Monotone W := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Icc_subset_Icc_right hab))
  have hWle : ∀ y, W y ≤ M := fun y => by
    show (μ (Icc 0 y)).toReal ≤ 1
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := Icc 0 y))
    simpa using this
  have hWw : M ≤ W w := by
    show (1 : ℝ) ≤ (μ (Icc 0 w)).toReal
    have h1 : (1 : ℝ≥0∞) ≤ μ (Icc 0 w) := hsupp ▸ measure_mono Ico_subset_Icc_self
    have := ENNReal.toReal_mono (measure_ne_top μ _) h1
    simpa using this
  have hW0 : ∀ y, 0 ≤ W y := fun y => ENNReal.toReal_nonneg
  -- chord bounds from concavity
  have hconcW : ConcaveOn ℝ (Icc 0 w) W := hconc
  have chord_right : ∀ y ∈ Icc m w, M - W y ≤ (M - W m) * ((w - y) / (w - m)) := by
    intro y hy
    have hwm : 0 < w - m := by linarith
    set l := (w - y) / (w - m) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith [hy.2]) hwm.le
    have hl1 : 1 - l = (y - m) / (w - m) := by rw [hl]; field_simp; ring
    have hpt : l * m + (1 - l) * w = y := by rw [hl1, hl]; field_simp; ring
    have hb0 : 0 ≤ 1 - l := by rw [hl1]; exact div_nonneg (by linarith [hy.1]) hwm.le
    have h1 : l • W m + (1 - l) • W w ≤ W (l • m + (1 - l) • w) :=
      hconcW.2 ⟨hm0.le, hmw.le⟩ ⟨hw0.le, le_rfl⟩ hl0 hb0 (by ring)
    simp only [smul_eq_mul] at h1
    rw [hpt] at h1
    have h2 : (1 - l) * M ≤ (1 - l) * W w := mul_le_mul_of_nonneg_left hWw hb0
    nlinarith
  have chord_left : ∀ y ∈ Icc 0 m, (M - W m) * ((w - y) / (w - m)) ≤ M - W y := by
    intro y hy
    have hwy : 0 < w - y := by linarith [hy.2]
    have hwm : 0 < w - m := by linarith
    set l := (w - m) / (w - y) with hl
    have hl0 : 0 ≤ l := div_nonneg hwm.le hwy.le
    have hl1 : 1 - l = (m - y) / (w - y) := by rw [hl]; field_simp; ring
    have hpt : l * y + (1 - l) * w = m := by rw [hl1, hl]; field_simp; ring
    have hb0 : 0 ≤ 1 - l := by rw [hl1]; exact div_nonneg (by linarith [hy.2]) hwy.le
    have h1 : l • W y + (1 - l) • W w ≤ W (l • y + (1 - l) • w) :=
      hconcW.2 ⟨hy.1, by linarith [hy.2]⟩ ⟨hw0.le, le_rfl⟩ hl0 hb0 (by ring)
    simp only [smul_eq_mul] at h1
    rw [hpt] at h1
    have h2 : (1 - l) * M ≤ (1 - l) * W w := mul_le_mul_of_nonneg_left hWw hb0
    have h3 : M - W m ≤ l * (M - W y) := by nlinarith
    have h4 : (M - W m) * ((w - y) / (w - m)) ≤ l * (M - W y) * ((w - y) / (w - m)) :=
      mul_le_mul_of_nonneg_right h3 (div_nonneg hwy.le hwm.le)
    have h5 : l * (M - W y) * ((w - y) / (w - m)) = M - W y := by
      rw [hl]; field_simp
    linarith
  -- split the loss
  have hsplit : ∀ x, p * max (m - x) 0 + h * max (x - m) 0
      = h * max (x - m) 0 + p * max (m - x) 0 := fun x => by ring
  have hint1 : IntegrableOn (fun x => max (x - m) 0) (Ico 0 w) μ := intOn_fin μ (by fun_prop) _ _
  have hint2 : IntegrableOn (fun x => max (m - x) 0) (Ico 0 w) μ := intOn_fin μ (by fun_prop) _ _
  have hI : ∫ x in Ico 0 w, (p * max (m - x) 0 + h * max (x - m) 0) ∂μ
      = h * ∫ x in Ico 0 w, max (x - m) 0 ∂μ + p * ∫ x in Ico 0 w, max (m - x) 0 ∂μ := by
    simp_rw [hsplit]
    rw [integral_add (hint1.const_mul h) (hint2.const_mul p), integral_const_mul,
      integral_const_mul]
  have hWint : ∀ a b : ℝ, IntegrableOn W (Icc a b) := fun a b =>
    (hWmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hconst : ∀ a b : ℝ, IntegrableOn (fun _ : ℝ => M) (Icc a b) := fun a b =>
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  -- lower hinge
  have hA : ∫ x in Ico 0 w, max (m - x) 0 ∂μ = ∫ y in Icc 0 m, W y := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => max (m - x) 0)
      (μ := μ.restrict (Ico 0 w)) (ae_of_all _ fun x => le_max_right (m - x) 0)
      (by fun_prop : Continuous fun x : ℝ => max (m - x) 0).aestronglyMeasurable]
    have e1 : ∀ x, ENNReal.ofReal (max (m - x) 0) = ENNReal.ofReal (m - x) := fun x => by
      rcases le_total (m - x) 0 with h' | h'
      · rw [max_eq_right h', ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h']
      · rw [max_eq_left h']
    simp_rw [e1]
    rw [tonelli_left μ m _ measurableSet_Ico]
    have e2 : ∫⁻ y in Iic m, μ (Ico 0 w ∩ Iic y) = ∫⁻ y in Icc 0 m, ENNReal.ofReal (W y) := by
      rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Icc]
      refine lintegral_congr fun y => ?_
      by_cases hym : y ≤ m
      · by_cases hy0 : 0 ≤ y
        · rw [indicator_of_mem (mem_Iic.2 hym), indicator_of_mem (mem_Icc.2 ⟨hy0, hym⟩)]
          have : Ico 0 w ∩ Iic y = Icc 0 y := by
            ext x
            simp only [mem_inter_iff, mem_Ico, mem_Iic, mem_Icc]
            constructor
            · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
          rw [this, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        · rw [indicator_of_mem (mem_Iic.2 hym), indicator_of_notMem (by
            simp only [mem_Icc, not_and, not_le]; intro h; linarith)]
          have : Ico 0 w ∩ Iic y = ∅ := by
            refine Set.eq_empty_of_forall_notMem fun x hx => ?_
            simp only [mem_inter_iff, mem_Ico, mem_Iic] at hx
            linarith [hx.1.1, hx.2]
          rw [this, measure_empty]
      · rw [indicator_of_notMem (by simpa using hym), indicator_of_notMem (by
          simp only [mem_Icc, not_and, not_le]; intro _; linarith)]
    rw [e2, ← ofReal_integral_eq_lintegral_ofReal (hWint 0 m)
      (ae_of_all _ fun y => hW0 y), ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Icc fun y _ => hW0 y)]
  -- upper hinge
  have hB : ∫ x in Ico 0 w, max (x - m) 0 ∂μ = ∫ y in Ico m w, (M - W y) := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => max (x - m) 0)
      (μ := μ.restrict (Ico 0 w)) (ae_of_all _ fun x => le_max_right (x - m) 0)
      (by fun_prop : Continuous fun x : ℝ => max (x - m) 0).aestronglyMeasurable]
    have e1 : ∀ x, ENNReal.ofReal (max (x - m) 0) = ENNReal.ofReal (x - m) := fun x => by
      rcases le_total (x - m) 0 with h' | h'
      · rw [max_eq_right h', ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h']
      · rw [max_eq_left h']
    simp_rw [e1]
    rw [tonelli_right μ m _ measurableSet_Ico]
    have hGnn : ∀ y ∈ Ico m w, 0 ≤ M - W y := fun y _ => by linarith [hWle y]
    have e2 : ∫⁻ y in Ici m, μ (Ico 0 w ∩ Ioi y)
        = ∫⁻ y in Ico m w, ENNReal.ofReal (M - W y) := by
      rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ico]
      refine lintegral_congr fun y => ?_
      by_cases hym : m ≤ y
      · by_cases hyw : y < w
        · rw [indicator_of_mem (mem_Ici.2 hym), indicator_of_mem (mem_Ico.2 ⟨hym, hyw⟩)]
          have hy0 : 0 ≤ y := by linarith
          have hset : Ico 0 w ∩ Ioi y = Ioo y w := by
            ext x
            simp only [mem_inter_iff, mem_Ico, mem_Ioi, mem_Ioo]
            constructor
            · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
          have hunion : Ico 0 w = Icc 0 y ∪ Ioo y w := by
            ext x
            simp only [mem_Ico, mem_union, mem_Icc, mem_Ioo]
            constructor
            · rintro ⟨h1, h2⟩
              rcases le_or_gt x y with hxy | hxy
              · exact Or.inl ⟨h1, hxy⟩
              · exact Or.inr ⟨hxy, h2⟩
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact ⟨h1, by linarith⟩
              · exact ⟨by linarith, h2⟩
          have hdisj : Disjoint (Icc 0 y) (Ioo y w) :=
            Set.disjoint_left.2 fun x h1 h2 => by simp only [mem_Icc, mem_Ioo] at h1 h2; linarith
          have hmeas := measure_union hdisj measurableSet_Ioo (μ := μ)
          rw [← hunion, hsupp] at hmeas
          have hreal : M = W y + (μ (Ioo y w)).toReal := by
            rw [hM]
            have := congrArg ENNReal.toReal hmeas
            rwa [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
              ENNReal.toReal_one] at this
          rw [hset, show M - W y = (μ (Ioo y w)).toReal by linarith,
            ENNReal.ofReal_toReal (measure_ne_top μ _)]
        · rw [indicator_of_mem (mem_Ici.2 hym), indicator_of_notMem (by
            simp only [mem_Ico, not_and, not_lt]; intro _; linarith)]
          have : Ico 0 w ∩ Ioi y = ∅ := by
            refine Set.eq_empty_of_forall_notMem fun x hx => ?_
            simp only [mem_inter_iff, mem_Ico, mem_Ioi] at hx
            linarith [hx.1.2, hx.2]
          rw [this, measure_empty]
      · rw [indicator_of_notMem (by simpa using hym), indicator_of_notMem (by
          simp only [mem_Ico, not_and, not_lt]; intro h; linarith)]
    have hGint : IntegrableOn (fun y => M - W y) (Ico m w) :=
      ((hconst m w).sub (hWint m w)).mono_set Ico_subset_Icc_self
    rw [e2, ← ofReal_integral_eq_lintegral_ofReal hGint
      ((ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ hGnn)), ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ico hGnn)]
  -- integrals of the chords
  have hwm : 0 < w - m := by linarith
  set Gm := M - W m with hGm
  have hGm0 : 0 ≤ Gm := by rw [hGm]; linarith [hWle m]
  have hlin : ∀ a b : ℝ, a ≤ b → ∫ y in Icc a b, Gm * ((w - y) / (w - m))
      = Gm / (w - m) * (w * (b - a) - (b ^ 2 - a ^ 2) / 2) := by
    intro a b hab
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have : (fun y => Gm * ((w - y) / (w - m))) = fun y => Gm / (w - m) * (w - y) := by
      ext y; ring
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const (intervalIntegral.intervalIntegrable_id), integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlinInt : ∀ a b : ℝ, IntegrableOn (fun y => Gm * ((w - y) / (w - m))) (Icc a b) := by
    intro a b
    exact (by fun_prop : Continuous fun y : ℝ => Gm * ((w - y) / (w - m))).integrableOn_Icc
  have hL : Gm / (w - m) * (w * m - m ^ 2 / 2) ≤ ∫ y in Icc 0 m, (M - W y) := by
    rw [show w * m - m ^ 2 / 2 = w * (m - 0) - (m ^ 2 - 0 ^ 2) / 2 by ring, ← hlin 0 m hm0.le]
    refine setIntegral_mono_on (hlinInt 0 m) ((hconst 0 m).sub (hWint 0 m))
      measurableSet_Icc fun y hy => chord_left y hy
  have hR : ∫ y in Ico m w, (M - W y) ≤ Gm / (w - m) * ((w - m) ^ 2 / 2) := by
    have e : Gm / (w - m) * ((w - m) ^ 2 / 2) = ∫ y in Icc m w, Gm * ((w - y) / (w - m)) := by
      rw [hlin m w hmw.le]; ring
    rw [e, integral_Icc_eq_integral_Ico]
    refine setIntegral_mono_on (((hconst m w).sub (hWint m w)).mono_set
      Ico_subset_Icc_self) ((hlinInt m w).mono_set Ico_subset_Icc_self)
      measurableSet_Ico fun y hy => chord_right y (Ico_subset_Icc_self hy)
  have hAeq : ∫ y in Icc 0 m, W y = m * M - ∫ y in Icc 0 m, (M - W y) := by
    rw [integral_sub (hconst 0 m) (hWint 0 m), setIntegral_const,
      smul_eq_mul, Real.volume_real_Icc_of_le hm0.le]
    ring
  have hcoef : h * (w - m) ^ 2 = p * (2 * w * m - m ^ 2) := by
    have e1 : w - m = w * σ := by rw [hm]; ring
    have e2 : 2 * w * m - m ^ 2 = w ^ 2 * (1 - σ ^ 2) := by rw [hm]; ring
    rw [e1, e2, mul_pow, hσsq]
    field_simp
    ring
  have hfinal : h * (∫ y in Ico m w, (M - W y)) + p * (∫ y in Icc 0 m, W y) ≤ p * m * M := by
    rw [hAeq]
    have h1 : h * (∫ y in Ico m w, (M - W y)) ≤ h * (Gm / (w - m) * ((w - m) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hR hh.le
    have h2 : p * (Gm / (w - m) * (w * m - m ^ 2 / 2)) ≤ p * ∫ y in Icc 0 m, (M - W y) :=
      mul_le_mul_of_nonneg_left hL hp.le
    have h3 : h * (Gm / (w - m) * ((w - m) ^ 2 / 2))
        = p * (Gm / (w - m) * (w * m - m ^ 2 / 2)) := by
      have : h * ((w - m) ^ 2 / 2) = p * (w * m - m ^ 2 / 2) := by nlinarith [hcoef]
      calc h * (Gm / (w - m) * ((w - m) ^ 2 / 2)) = Gm / (w - m) * (h * ((w - m) ^ 2 / 2)) := by ring
        _ = Gm / (w - m) * (p * (w * m - m ^ 2 / 2)) := by rw [this]
        _ = p * (Gm / (w - m) * (w * m - m ^ 2 / 2)) := by ring
    nlinarith
  rw [hI, hA, hB]
  have : p * (1 - σ) * w = p * m * M := by rw [hm, hM]; ring
  rw [this]
  linarith

end NDM

open NDM in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (h p w : ℝ) (hh : 0 < h)
    (hp : 0 < p) (hw : 0 ≤ w) (c : ℝ≥0∞) (ϱ : ℝ → ℝ≥0∞) (hϱ : AntitoneOn ϱ (Set.Ioo 0 w))
    (hlaw : P.map Y = c • Measure.dirac 0 + (volume.restrict (Set.Ioo 0 w)).withDensity ϱ) :
    ⨅ z : ℝ, ∫ ω, (p * max (z - Y ω) 0 + h * max (Y ω - z) 0) ∂P
      ≤ p * (1 - Real.sqrt (p / (p + h))) * w := by
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure ℝ, μ = P.map Y := ⟨_, rfl⟩
  rw [← hμdef] at hlaw
  have : IsProbabilityMeasure μ := by rw [hμdef]; exact Measure.isProbabilityMeasure_map hY.aemeasurable
  have hL0 : ∀ z y : ℝ, 0 ≤ p * max (z - y) 0 + h * max (y - z) 0 := fun z y =>
    add_nonneg (mul_nonneg hp.le (le_max_right _ _)) (mul_nonneg hh.le (le_max_right _ _))
  have hBdd : BddBelow (Set.range fun z : ℝ =>
      ∫ ω, (p * max (z - Y ω) 0 + h * max (Y ω - z) 0) ∂P) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact integral_nonneg fun ω => hL0 z (Y ω)⟩
  refine (ciInf_le hBdd (w * (1 - Real.sqrt (p / (p + h))))).trans ?_
  have hmap : ∀ z : ℝ, ∫ ω, (p * max (z - Y ω) 0 + h * max (Y ω - z) 0) ∂P
      = ∫ y, (p * max (z - y) 0 + h * max (y - z) 0) ∂μ := fun z => by
    rw [hμdef, integral_map hY.aemeasurable
      (by fun_prop : Continuous fun y : ℝ => p * max (z - y) 0 + h * max (y - z) 0).aestronglyMeasurable]
  rw [hmap]
  -- the law of `Y`
  have hμA : ∀ A : Set ℝ, MeasurableSet A →
      μ A = c * A.indicator 1 (0 : ℝ) + ∫⁻ t in A ∩ Ioo 0 w, ϱ t := by
    intro A hA
    rw [hlaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA]
  rcases hw.lt_or_eq with hw0 | hw0
  · -- `μ` is carried by `[0, w)`
    have hsupp : μ (Ico 0 w) = 1 := by
      refine (prob_compl_eq_zero_iff measurableSet_Ico).1 ?_
      rw [hμA _ measurableSet_Ico.compl, indicator_of_notMem (Set.notMem_compl_iff.2 (show (0 : ℝ) ∈ Ico 0 w from ⟨le_rfl, hw0⟩)),
        mul_zero, zero_add]
      have : (Ico 0 w)ᶜ ∩ Ioo 0 w = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => hx.1 (Ioo_subset_Ico_self hx.2)
      rw [this, Measure.restrict_empty, lintegral_zero_measure]
    -- the distribution function is concave on `[0, w]`
    set W : ℝ → ℝ := fun y => (μ (Icc 0 y)).toReal with hWdef
    have hIoc : ∀ a b : ℝ, 0 ≤ a → μ (Ioc a b) = ∫⁻ t in Ioc a b ∩ Ioo 0 w, ϱ t := by
      intro a b ha
      rw [hμA _ measurableSet_Ioc, indicator_of_notMem (fun h0 => absurd h0.1 (not_lt.2 ha)),
        mul_zero, zero_add]
    have hWdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b → W b - W a = (μ (Ioc a b)).toReal := by
      intro a b ha hab
      have hu : Icc 0 a ∪ Ioc a b = Icc 0 b := Icc_union_Ioc_eq_Icc ha hab
      have hd : Disjoint (Icc 0 a) (Ioc a b) :=
        Set.disjoint_left.2 fun x h1 h2 => by
          simp only [mem_Icc, mem_Ioc] at h1 h2; linarith [h1.2, h2.1]
      have hmu := measure_union hd measurableSet_Ioc (μ := μ)
      rw [hu] at hmu
      show (μ (Icc 0 b)).toReal - (μ (Icc 0 a)).toReal = _
      rw [hmu, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring
    have hconc : ConcaveOn ℝ (Icc 0 w) W := by
      refine concaveOn_of_slope_anti_adjacent (convex_Icc 0 w) ?_
      intro x y z hx hz hxy hyz
      have hy0 : 0 < y := lt_of_le_of_lt hx.1 hxy
      have hyw : y < w := lt_of_lt_of_le hyz hz.2
      have hyI : y ∈ Ioo 0 w := ⟨hy0, hyw⟩
      have hlow : ϱ y * ENNReal.ofReal (y - x) ≤ μ (Ioc x y) := by
        rw [hIoc x y hx.1]
        calc ϱ y * ENNReal.ofReal (y - x) = ∫⁻ _t in Ioo x y, ϱ y := by
              rw [setLIntegral_const, Real.volume_Ioo]
          _ ≤ ∫⁻ t in Ioo x y, ϱ t := setLIntegral_mono' measurableSet_Ioo fun t ht =>
              hϱ ⟨lt_of_le_of_lt hx.1 ht.1, lt_trans ht.2 hyw⟩ hyI ht.2.le
          _ ≤ ∫⁻ t in Ioc x y ∩ Ioo 0 w, ϱ t := lintegral_mono_set fun t ht =>
              ⟨⟨ht.1, ht.2.le⟩, lt_of_le_of_lt hx.1 ht.1, lt_trans ht.2 hyw⟩
      have hup : μ (Ioc y z) ≤ ϱ y * ENNReal.ofReal (z - y) := by
        rw [hIoc y z hy0.le]
        calc ∫⁻ t in Ioc y z ∩ Ioo 0 w, ϱ t ≤ ∫⁻ _t in Ioc y z ∩ Ioo 0 w, ϱ y :=
              setLIntegral_mono' (measurableSet_Ioc.inter measurableSet_Ioo) fun t ht =>
                hϱ hyI ht.2 ht.1.1.le
          _ = ϱ y * volume (Ioc y z ∩ Ioo 0 w) := setLIntegral_const _ _
          _ ≤ ϱ y * volume (Ioc y z) := mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) (by positivity)
          _ = ϱ y * ENNReal.ofReal (z - y) := by rw [Real.volume_Ioc]
      have hfin : ϱ y ≠ ∞ := by
        intro htop
        have h1 : μ (Ioc x y) ≤ 1 := prob_le_one
        rw [htop, ENNReal.top_mul (ENNReal.ofReal_pos.2 (sub_pos.2 hxy)).ne'] at hlow
        exact absurd (hlow.trans h1) (by simp)
      have hlowR : (ϱ y).toReal * (y - x) ≤ W y - W x := by
        rw [hWdiff x y hx.1 hxy.le]
        have := ENNReal.toReal_mono (measure_ne_top μ _) hlow
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
      have hupR : W z - W y ≤ (ϱ y).toReal * (z - y) := by
        rw [hWdiff y z hy0.le hyz.le]
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top) hup
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have k1 := mul_le_mul_of_nonneg_right hupR (by linarith : (0 : ℝ) ≤ y - x)
      have k2 := mul_le_mul_of_nonneg_right hlowR (by linarith : (0 : ℝ) ≤ z - y)
      nlinarith
    exact core μ h p w hh hp hw0 hsupp hconc
  · -- `w = 0`: `Y = 0` almost surely and the loss vanishes at the target `0`
    subst hw0
    have h0 : μ {0}ᶜ = 0 := by
      rw [hμA _ (measurableSet_singleton 0).compl, indicator_of_notMem (Set.notMem_compl_iff.2 (Set.mem_singleton 0)),
        mul_zero, zero_add, Ioo_self, inter_empty, Measure.restrict_empty, lintegral_zero_measure]
    have hae : ∀ᵐ y ∂μ, y = 0 := by
      rw [ae_iff]; exact h0
    rw [integral_eq_zero_of_ae (hae.mono fun y hy => by rw [hy]; simp)]
    simp
