-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma13_twoPoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:33:06.101144+00:00
-- url     : https://prove2.me/submissions/9b071b96-b1d6-4dfc-8063-9cf4b4f01955

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


theorem solution {Omega : Type*} [MeasurableSpace Omega]
    (p0 p1 : Measure Omega) [IsProbabilityMeasure p0] [IsProbabilityMeasure p1]
    (hclose : classicalTVDistance p0 p1 < 1 / 3) :
    ¬ ∃ A : Omega → ℝ, Measurable A ∧ (∀ x, 0 ≤ A x ∧ A x ≤ 1) ∧
      (2 / 3 : ℝ) ≤ (∫ x, 1 - A x ∂p0) ∧
      (2 / 3 : ℝ) ≤ (∫ x, A x ∂p1) := by
  rintro ⟨A, hA, hA01, h0, h1⟩
  set TV := classicalTVDistance p0 p1 with hTV
  have hbdd : BddAbove {v : ℝ | ∃ S : Set Omega, MeasurableSet S ∧
      v = |(p0 S).toReal - (p1 S).toReal|} := by
    refine ⟨1, ?_⟩
    rintro v ⟨S, -, rfl⟩
    have a0 : (p0 S).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have a1 : (p1 S).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    rw [abs_le]; constructor <;> linarith [ENNReal.toReal_nonneg (a := p0 S), ENNReal.toReal_nonneg (a := p1 S)]
  have hset : ∀ S, MeasurableSet S → |(p0 S).toReal - (p1 S).toReal| ≤ TV :=
    fun S hS => le_csSup hbdd ⟨S, hS, rfl⟩
  have hTV0 : 0 ≤ TV := (abs_nonneg _).trans (hset ∅ MeasurableSet.empty)
  have hS1 : ∀ S, MeasurableSet S → p1 S ≤ p0 S + ENNReal.ofReal TV := by
    intro S hS
    have := hset S hS
    rw [abs_le] at this
    rw [← ENNReal.ofReal_toReal (measure_ne_top p1 S), ← ENNReal.ofReal_toReal (measure_ne_top p0 S),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hTV0]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hnn0 : 0 ≤ᵐ[p0] A := Filter.Eventually.of_forall fun x => (hA01 x).1
  have hnn1 : 0 ≤ᵐ[p1] A := Filter.Eventually.of_forall fun x => (hA01 x).1
  have hanti : ∀ (μ : Measure Omega), Antitone (fun t : ℝ => μ {a | t < A a}) := by
    intro μ s t hst
    exact measure_mono (fun a (ha : t < A a) => (lt_of_le_of_lt hst ha : s < A a))
  have hL : ∫⁻ x, ENNReal.ofReal (A x) ∂p1 ≤ ∫⁻ x, ENNReal.ofReal (A x) ∂p0 + ENNReal.ofReal TV := by
    rw [lintegral_eq_lintegral_meas_lt p1 hnn1 hA.aemeasurable,
      lintegral_eq_lintegral_meas_lt p0 hnn0 hA.aemeasurable]
    calc ∫⁻ t in Set.Ioi 0, p1 {a | t < A a}
        ≤ ∫⁻ t in Set.Ioi 0, (p0 {a | t < A a} +
            (Set.Ioc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal TV) t) := by
          apply setLIntegral_mono ((hanti p0).measurable.add (measurable_const.indicator measurableSet_Ioc))
          intro t ht
          simp only [Pi.add_apply]
          by_cases h : t < 1
          · rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) 1 from ⟨ht, h.le⟩)]
            exact hS1 _ (measurableSet_lt measurable_const hA)
          · have : {a | t < A a} = ∅ := by
              ext a; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
              linarith [(hA01 a).2, not_lt.mp h]
            rw [this, measure_empty]; exact bot_le
      _ = (∫⁻ t in Set.Ioi 0, p0 {a | t < A a}) + ∫⁻ t in Set.Ioi 0,
            (Set.Ioc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal TV) t :=
          lintegral_add_left (hanti p0).measurable _
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
          calc ENNReal.ofReal TV * volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi 0)
              ≤ ENNReal.ofReal TV * volume (Set.Ioc (0 : ℝ) 1) :=
                mul_le_mul (le_refl _) (measure_mono Set.inter_subset_left) bot_le bot_le
            _ = ENNReal.ofReal TV := by simp
  have hfin : ∀ (μ : Measure Omega) [IsProbabilityMeasure μ],
      ∫⁻ x, ENNReal.ofReal (A x) ∂μ ≠ ⊤ := by
    intro μ _
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂μ) (by simp) (lintegral_mono fun x => ?_)
    simpa using (hA01 x).2
  have hI0 := integral_eq_lintegral_of_nonneg_ae hnn0 hA.aestronglyMeasurable
  have hI1 := integral_eq_lintegral_of_nonneg_ae hnn1 hA.aestronglyMeasurable
  have hR : ∫ x, A x ∂p1 ≤ ∫ x, A x ∂p0 + TV := by
    rw [hI0, hI1]
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin p0, ENNReal.ofReal_ne_top⟩) hL
    rwa [ENNReal.toReal_add (hfin p0) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hTV0] at this
  have hint : Integrable A p0 := by
    refine Integrable.of_bound hA.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hA01 x]
  have h0' : ∫ x, 1 - A x ∂p0 = 1 - ∫ x, A x ∂p0 := by
    rw [integral_sub (integrable_const 1) hint]; simp
  rw [h0'] at h0
  linarith

end
