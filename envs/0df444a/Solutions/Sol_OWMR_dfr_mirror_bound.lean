-- Prove2me | solution 1 for OWMR.dfr_mirror_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:50.166653+00:00
-- url     : https://prove2.me/submissions/1e1ae435-c1d3-4ce6-ae52-21ec082170ec

import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace DFRMir

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

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ OWMR.renewalMeasure ρ (Set.Ico 0 w) := by
  unfold OWMR.renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma mirrorAvg_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    OWMR.mirrorAvg ρ h p s S a = OWMR.ssAvgCost ρ (fun y => OWMR.whLoss h p (a - y)) 0 s S := by
  unfold OWMR.mirrorAvg OWMR.ssAvgCost OWMR.ssPeriodCost
  simp only [zero_mul, zero_add]

lemma bdd_of_cont {φ : ℝ → ℝ} (hφ : Continuous φ) (c e : ℝ) :
    ∃ C, ∀ y ∈ Set.Icc c e, φ y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

lemma intOn (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {a e : ℝ} (ha : 0 ≤ a) :
    IntegrableOn φ (Set.Ico a e) (OWMR.renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C)
    (ne_top_of_le_ne_top (OWMR.renewalMeasure_Ico_lt_top ρ hρ e).ne
      (measure_mono (Set.Ico_subset_Ico_left ha))) hφ.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hC x (Set.Ico_subset_Icc_self hx)

end DFRMir

set_option maxHeartbeats 4000000 in
open DFRMir in
theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (h p s S : ℝ) (hh : 0 < h) (hp : 0 < p) (hsS : s < S)
    (hconc : ConcaveOn ℝ (Set.Icc 0 (S - s))
      (fun x => (OWMR.renewalMeasure ρ (Set.Icc 0 x)).toReal)) :
    OWMR.mirrorCost ρ h p s S ≤ ENNReal.ofReal (p * (1 - Real.sqrt (p / (p + h))) * (S - s)) := by
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = S - s := ⟨_, rfl⟩
  rw [← hw] at hconc ⊢
  have hw0 : 0 < w := by rw [hw]; linarith
  set U := OWMR.renewalMeasure ρ with hUdef
  haveI : SFinite U := by rw [hUdef]; unfold OWMR.renewalMeasure; infer_instance
  have hUfin : ∀ b : ℝ, U (Set.Ico 0 b) ≠ ∞ := fun b => (OWMR.renewalMeasure_Ico_lt_top ρ hρ b).ne
  have hUw : U (Set.Ico 0 w) ≠ ∞ := hUfin w
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (U (Set.Ico 0 w)).toReal := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    have := ENNReal.toReal_mono hUw (one_le_renewal ρ w hw0)
    simpa [hM] using this
  have hM0 : 0 < M := by linarith
  -- the center parameters
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (p / (p + h)) := ⟨_, rfl⟩
  have hpph : 0 < p / (p + h) := div_pos hp (by linarith)
  have hσ0 : 0 < σ := by rw [hσ]; exact Real.sqrt_pos.2 hpph
  have hσsq : σ ^ 2 = p / (p + h) := by rw [hσ]; exact Real.sq_sqrt hpph.le
  have hσ1 : σ < 1 := by
    have : p / (p + h) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = w * (1 - σ) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact mul_pos hw0 (by linarith)
  have hmw : m < w := by rw [hm]; nlinarith
  -- `W y = U[0, y]`
  set W : ℝ → ℝ := fun y => (U (Set.Icc 0 y)).toReal with hWdef
  have hUIcc : ∀ y, y < w → U (Set.Icc 0 y) ≠ ∞ := fun y hy =>
    ne_top_of_le_ne_top hUw (measure_mono (Set.Icc_subset_Ico_right hy))
  have hWmono : Monotone W := by
    intro a b hab
    simp only [hWdef]
    by_cases hb : b < w
    · exact ENNReal.toReal_mono (hUIcc b hb) (measure_mono (Set.Icc_subset_Icc_right hab))
    · have hfin : U (Set.Icc 0 b) ≠ ∞ :=
        ne_top_of_le_ne_top (hUfin (b + 1)) (measure_mono (Set.Icc_subset_Ico_right (by linarith)))
      exact ENNReal.toReal_mono hfin (measure_mono (Set.Icc_subset_Icc_right hab))
  have hWle : ∀ y, y < w → W y ≤ M := fun y hy => by
    simp only [hWdef, hM]
    exact ENNReal.toReal_mono hUw (measure_mono (Set.Icc_subset_Ico_right hy))
  have hWw : M ≤ W w := by
    simp only [hWdef, hM]
    have hfin : U (Set.Icc 0 w) ≠ ∞ :=
      ne_top_of_le_ne_top (hUfin (w + 1)) (measure_mono (Set.Icc_subset_Ico_right (by linarith)))
    exact ENNReal.toReal_mono hfin (measure_mono Set.Ico_subset_Icc_self)
  have hW0 : ∀ y, 0 ≤ W y := fun y => ENNReal.toReal_nonneg
  -- chord bounds from concavity
  have hconcW : ConcaveOn ℝ (Set.Icc 0 w) W := hconc
  have chord_right : ∀ y ∈ Set.Icc m w, M - W y ≤ (M - W m) * ((w - y) / (w - m)) := by
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
    have h2 : (1 - l) * M ≤ (1 - l) * W w :=
      mul_le_mul_of_nonneg_left hWw (by rw [hl1]; exact div_nonneg (by linarith [hy.1]) hwm.le)
    nlinarith
  have chord_left : ∀ y ∈ Set.Icc 0 m, (M - W m) * ((w - y) / (w - m)) ≤ M - W y := by
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
    have h2 : (1 - l) * M ≤ (1 - l) * W w :=
      mul_le_mul_of_nonneg_left hWw (by rw [hl1]; exact div_nonneg (by linarith [hy.2]) hwy.le)
    -- M - W m ≤ l (M - W y)
    have h3 : M - W m ≤ l * (M - W y) := by nlinarith
    have h4 : (M - W m) * ((w - y) / (w - m)) ≤ l * (M - W y) * ((w - y) / (w - m)) :=
      mul_le_mul_of_nonneg_right h3 (div_nonneg hwy.le hwm.le)
    have h5 : l * (M - W y) * ((w - y) / (w - m)) = M - W y := by
      rw [hl]; field_simp
    linarith
  -- the loss at the center `S - m`
  have hφc : Continuous fun y => OWMR.whLoss h p ((S - m) - y) := by unfold OWMR.whLoss; fun_prop
  have hφ0 : ∀ y, 0 ≤ OWMR.whLoss h p ((S - m) - y) := fun y =>
    add_nonneg (mul_nonneg hh.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))
  have hmir : OWMR.mirrorAvg ρ h p s S (S - m) = ENNReal.ofReal
      ((∫ x in Set.Ico 0 w, OWMR.whLoss h p ((S - m) - (S - x)) ∂U) / M) := by
    rw [mirrorAvg_eq, OWMR.ss_renewal_reward ρ hρ _ hφc.measurable hφ0 0 s S le_rfl hsS
      (bdd_of_cont hφc s S), zero_add, ← hw, ← hM]
  have hsplit : ∀ x, OWMR.whLoss h p ((S - m) - (S - x))
      = h * max (x - m) 0 + p * max (m - x) 0 := by
    intro x
    unfold OWMR.whLoss
    rw [show S - m - (S - x) = x - m by ring, show -(x - m) = m - x by ring]
  have hint1 : IntegrableOn (fun x => max (x - m) 0) (Ico 0 w) U :=
    intOn ρ hρ (by fun_prop) le_rfl
  have hint2 : IntegrableOn (fun x => max (m - x) 0) (Ico 0 w) U :=
    intOn ρ hρ (by fun_prop) le_rfl
  have hI : ∫ x in Ico 0 w, OWMR.whLoss h p ((S - m) - (S - x)) ∂U
      = h * ∫ x in Ico 0 w, max (x - m) 0 ∂U + p * ∫ x in Ico 0 w, max (m - x) 0 ∂U := by
    simp_rw [hsplit]
    rw [integral_add (hint1.const_mul h) (hint2.const_mul p), integral_const_mul,
      integral_const_mul]
  have hWint : ∀ a b : ℝ, IntegrableOn W (Icc a b) := fun a b =>
    (hWmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hconst : ∀ a b : ℝ, IntegrableOn (fun _ : ℝ => M) (Icc a b) := fun a b =>
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  -- lower hinge
  have hA : ∫ x in Ico 0 w, max (m - x) 0 ∂U = ∫ y in Icc 0 m, W y := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => max (m - x) 0)
      (μ := U.restrict (Ico 0 w)) (ae_of_all _ fun x => le_max_right (m - x) 0)
      (by fun_prop : Continuous fun x : ℝ => max (m - x) 0).aestronglyMeasurable]
    have e1 : ∀ x, ENNReal.ofReal (max (m - x) 0) = ENNReal.ofReal (m - x) := fun x => by
      rcases le_total (m - x) 0 with h' | h'
      · rw [max_eq_right h', ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h']
      · rw [max_eq_left h']
    simp_rw [e1]
    rw [tonelli_left U m _ measurableSet_Ico]
    have e2 : ∫⁻ y in Iic m, U (Ico 0 w ∩ Iic y) = ∫⁻ y in Icc 0 m, ENNReal.ofReal (W y) := by
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
          rw [this, ENNReal.ofReal_toReal (hUIcc y (by linarith))]
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
  have hB : ∫ x in Ico 0 w, max (x - m) 0 ∂U = ∫ y in Ico m w, (M - W y) := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => max (x - m) 0)
      (μ := U.restrict (Ico 0 w)) (ae_of_all _ fun x => le_max_right (x - m) 0)
      (by fun_prop : Continuous fun x : ℝ => max (x - m) 0).aestronglyMeasurable]
    have e1 : ∀ x, ENNReal.ofReal (max (x - m) 0) = ENNReal.ofReal (x - m) := fun x => by
      rcases le_total (x - m) 0 with h' | h'
      · rw [max_eq_right h', ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h']
      · rw [max_eq_left h']
    simp_rw [e1]
    rw [tonelli_right U m _ measurableSet_Ico]
    have hGnn : ∀ y ∈ Ico m w, 0 ≤ M - W y := fun y hy => by linarith [hWle y hy.2]
    have e2 : ∫⁻ y in Ici m, U (Ico 0 w ∩ Ioi y)
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
          have hmeas := measure_union hdisj measurableSet_Ioo (μ := U)
          rw [← hunion] at hmeas
          have hfin2 : U (Ioo y w) ≠ ∞ :=
            ne_top_of_le_ne_top hUw (measure_mono (fun x hx => by
              simp only [mem_Ioo, mem_Ico] at hx ⊢; exact ⟨by linarith, hx.2⟩))
          have hreal : M = W y + (U (Ioo y w)).toReal := by
            rw [hM, hmeas, ENNReal.toReal_add (hUIcc y hyw) hfin2]
          rw [hset, show M - W y = (U (Ioo y w)).toReal by linarith, ENNReal.ofReal_toReal hfin2]
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
  have hGm0 : 0 ≤ Gm := by rw [hGm]; linarith [hWle m hmw]
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
  -- lower part
  have hL : Gm / (w - m) * (w * m - m ^ 2 / 2) ≤ ∫ y in Icc 0 m, (M - W y) := by
    rw [show w * m - m ^ 2 / 2 = w * (m - 0) - (m ^ 2 - 0 ^ 2) / 2 by ring, ← hlin 0 m hm0.le]
    refine setIntegral_mono_on (hlinInt 0 m) ((hconst 0 m).sub (hWint 0 m))
      measurableSet_Icc fun y hy => chord_left y hy
  -- upper part
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
  -- the coefficient identity `h (w-m)^2 = p (2wm - m^2)`
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
  calc OWMR.mirrorCost ρ h p s S ≤ OWMR.mirrorAvg ρ h p s S (S - m) :=
        iInf_le (fun a => OWMR.mirrorAvg ρ h p s S a) (S - m)
    _ = ENNReal.ofReal ((∫ x in Set.Ico 0 w, OWMR.whLoss h p ((S - m) - (S - x)) ∂U) / M) := hmir
    _ ≤ ENNReal.ofReal (p * (1 - Real.sqrt (p / (p + h))) * w) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hM0, hI, hA, hB, ← hσ]
        have : p * (1 - σ) * w = p * m := by rw [hm]; ring
        rw [this]
        linarith
