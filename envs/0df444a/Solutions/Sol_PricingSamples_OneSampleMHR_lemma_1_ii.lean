-- Prove2me | solution 1 for PricingSamples.OneSampleMHR.lemma_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:07:10.810512+00:00
-- url     : https://prove2.me/submissions/58526504-c4ab-4d79-8664-38e929c811c7

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

namespace PSMQ

open MeasureTheory PricingSamples.OneSampleMHR ProbabilityTheory Set

lemma ccdf_anti (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (ccdf μ) := by
  intro x y h
  unfold ccdf
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ioi_subset_Ioi h))

lemma ccdf_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ ccdf μ x := ENNReal.toReal_nonneg

lemma ccdf_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) : ccdf μ x ≤ 1 := by
  unfold ccdf
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma ccdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) : ccdf μ x = 1 - cdf μ x := by
  rw [cdf_eq_real]
  unfold ccdf
  rw [← Set.compl_Iic, ← measureReal_def, measureReal_compl measurableSet_Iic, probReal_univ]

lemma ccdf_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume) :
    Continuous (ccdf μ) := by
  have hcont : ∀ x, ContinuousAt (cdf μ) x := by
    intro x
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · rw [← continuousWithinAt_Iio_iff_Iic, (monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq]
      have h1 := (cdf μ).measure_singleton x
      rw [measure_cdf, hac (Real.volume_singleton)] at h1
      have h2 := ENNReal.ofReal_eq_zero.mp h1.symm
      have h3 : Function.leftLim (cdf μ) x ≤ cdf μ x := (monotone_cdf μ).leftLim_le le_rfl
      linarith
    · exact (cdf μ).right_continuous x
  have : ccdf μ = fun x => 1 - cdf μ x := funext (ccdf_eq μ)
  rw [this]
  exact continuous_const.sub (continuous_iff_continuousAt.mpr hcont)

lemma mu_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume) {a b : ℝ} (hab : a ≤ b) :
    μ (Icc a b) = ENNReal.ofReal (ccdf μ a - ccdf μ b) := by
  have h0 : μ {a} = 0 := hac (Real.volume_singleton)
  rw [← measure_congr (Ioc_ae_eq_Icc' h0)]
  have e : Ioc a b = Ioi a \ Ioi b := by
    ext x; simp only [mem_Ioc, mem_diff, mem_Ioi, not_lt]
  rw [e, measure_diff (Ioi_subset_Ioi hab) measurableSet_Ioi.nullMeasurableSet (measure_ne_top μ _)]
  unfold ccdf
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top μ _),
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- left-continuous quantile of `μ` restricted to `[w, w']`. -/
noncomputable def Q (μ : Measure ℝ) (w w' u : ℝ) : ℝ :=
  sInf {s | s ∈ Icc w w' ∧ ccdf μ s ≤ max u (ccdf μ w')}

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume) {w w' : ℝ} (hww : w ≤ w')
include hww

lemma Qset_nonempty (u : ℝ) : {s | s ∈ Icc w w' ∧ ccdf μ s ≤ max u (ccdf μ w')}.Nonempty :=
  ⟨w', ⟨le_refl _ |> fun h => ⟨hww, h⟩, le_max_right _ _⟩⟩

lemma Qset_bdd (u : ℝ) : BddBelow {s | s ∈ Icc w w' ∧ ccdf μ s ≤ max u (ccdf μ w')} :=
  ⟨w, fun s hs => hs.1.1⟩

include hac in
lemma Q_mem (u : ℝ) : Q μ w w' u ∈ Icc w w' ∧ ccdf μ (Q μ w w' u) ≤ max u (ccdf μ w') := by
  have hcl : IsClosed {s | s ∈ Icc w w' ∧ ccdf μ s ≤ max u (ccdf μ w')} :=
    isClosed_Icc.inter (isClosed_le (ccdf_continuous μ hac) continuous_const)
  exact hcl.csInf_mem (Qset_nonempty μ hww u) (Qset_bdd μ hww u)

lemma Q_le {u t : ℝ} (ht : t ∈ Icc w w') (h : ccdf μ t ≤ max u (ccdf μ w')) : Q μ w w' u ≤ t :=
  csInf_le (Qset_bdd μ hww u) ⟨ht, h⟩

lemma Q_anti : Antitone (Q μ w w') := by
  intro u u' huu
  apply csInf_le_csInf (Qset_bdd μ hww u') (Qset_nonempty μ hww u)
  intro s hs
  exact ⟨hs.1, le_trans hs.2 (max_le_max huu le_rfl)⟩

include hac in
lemma ccdf_Q {u : ℝ} (hu1 : ccdf μ w' ≤ u) (hu2 : u ≤ ccdf μ w) : ccdf μ (Q μ w w' u) = u := by
  have hm := Q_mem μ hac hww u
  have hmax : max u (ccdf μ w') = u := max_eq_left hu1
  rw [hmax] at hm
  apply le_antisymm hm.2
  rcases hm.1.1.eq_or_lt with h | h
  · rw [← h]; exact hu2
  · have hcl : IsClosed {s | u ≤ ccdf μ s} := isClosed_le continuous_const (ccdf_continuous μ hac)
    have hsub : Ico w (Q μ w w' u) ⊆ {s | u ≤ ccdf μ s} := by
      intro s hs
      by_contra hc
      simp only [mem_setOf_eq, not_le] at hc
      have := Q_le μ hww (⟨hs.1, le_trans hs.2.le hm.1.2⟩ : s ∈ Icc w w') (by rw [hmax]; exact hc.le)
      exact absurd hs.2 (not_lt.mpr this)
    have := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ico h.ne] at this
    exact this ⟨h.le, le_rfl⟩

include hac in
lemma Q_le_iff {u t : ℝ} (hu1 : ccdf μ w' ≤ u) (ht : t ∈ Icc w w') :
    Q μ w w' u ≤ t ↔ ccdf μ t ≤ u := by
  have hmax : max u (ccdf μ w') = u := max_eq_left hu1
  constructor
  · intro h
    have hm := Q_mem μ hac hww u
    rw [hmax] at hm
    exact le_trans (ccdf_anti μ h) hm.2
  · intro h
    exact Q_le μ hww ht (by rw [hmax]; exact h)

include hac in
lemma map_Q : Measure.map (Q μ w w') (volume.restrict (Icc (ccdf μ w') (ccdf μ w))) =
    μ.restrict (Icc w w') := by
  have hQm : Measurable (Q μ w w') := (Q_anti μ hww).measurable
  haveI : IsFiniteMeasure (Measure.map (Q μ w w') (volume.restrict (Icc (ccdf μ w') (ccdf μ w)))) :=
    inferInstance
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  rw [Measure.map_apply hQm measurableSet_Iic, Measure.restrict_apply (hQm measurableSet_Iic),
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge t w with htw | htw
  · have e1 : Q μ w w' ⁻¹' Iic t ∩ Icc (ccdf μ w') (ccdf μ w) = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro h
      have := (Q_mem μ hac hww u).1.1
      linarith
    have e2 : Iic t ∩ Icc w w' = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [e1, e2]; simp
  · set t' := min t w' with ht'
    have ht'm : t' ∈ Icc w w' := ⟨le_min htw hww, min_le_right _ _⟩
    have e1 : Q μ w w' ⁻¹' Iic t ∩ Icc (ccdf μ w') (ccdf μ w) = Icc (ccdf μ t') (ccdf μ w) := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have h4 : Q μ w w' u ≤ t' := le_min h1 (Q_mem μ hac hww u).1.2
        exact ⟨(Q_le_iff μ hac hww h2 ht'm).mp h4, h3⟩
      · rintro ⟨h1, h3⟩
        have h2 : ccdf μ w' ≤ u := le_trans (ccdf_anti μ ht'm.2) h1
        have h4 := (Q_le_iff μ hac hww h2 ht'm).mpr h1
        exact ⟨le_trans h4 (min_le_left _ _), h2, h3⟩
    have e2 : Iic t ∩ Icc w w' = Icc w t' := by
      ext s
      simp only [mem_inter_iff, mem_Iic, mem_Icc, ht', le_min_iff]
      tauto
    rw [e1, e2, Real.volume_Icc, mu_Icc μ hac ht'm.1]

end

end PSMQ

open MeasureTheory PricingSamples.OneSampleMHR PSMQ Set

theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) (hF : InFAlpha α μ)
    (g : ℝ → ℝ) (hg_meas : Measurable g) (hg : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g q)
    (γ w w' : ℝ) (hγ : 0 < γ) (hw : 0 ≤ w) (hww' : w < w')
    (Hl : ℝ → ℝ) (hHl_anti : AntitoneOn Hl (Set.Ici 0))
    (hHl_range : ∀ v, 0 ≤ v → Hl v ∈ Set.Icc (0 : ℝ) 1)
    (hHl : ∀ v ∈ Set.Icc (γ * w) (γ * w'), Hl v ≤ ccdf μ v)
    (hvHl : AntitoneOn (fun v => v * Hl v) (Set.Icc (γ * w) (γ * w')))
    (Hu : ℝ → ℝ) (hHu_anti : AntitoneOn Hu (Set.Ici 0))
    (hHu_range : ∀ v, 0 ≤ v → Hu v ∈ Set.Icc (0 : ℝ) 1)
    (hHu : ∀ v ∈ Set.Icc w w', ccdf μ v ≤ Hu v) (hHu_w : Hu w = ccdf μ w) :
    ∫⁻ q in Set.Icc (ccdf μ w') (ccdf μ w),
        ENNReal.ofReal (γ * minGenInv w' Hu q * Hl (γ * minGenInv w' Hu q) * g q) ≤
      ∫⁻ s in Set.Icc w w', ENNReal.ofReal (γ * s * ccdf μ (γ * s) * g (ccdf μ s)) ∂μ := by
  obtain ⟨⟨hprob, -, -, -⟩, hac, -⟩ := hF
  have hc : Measurable (ccdf μ) := (ccdf_anti μ).measurable
  have hf : Measurable (fun s => ENNReal.ofReal (γ * s * ccdf μ (γ * s) * g (ccdf μ s))) :=
    ENNReal.measurable_ofReal.comp (((measurable_const.mul measurable_id).mul
      (hc.comp (measurable_const.mul measurable_id))).mul (hg_meas.comp hc))
  rw [← map_Q μ hac hww'.le, lintegral_map hf (Q_anti μ hww'.le).measurable]
  apply lintegral_mono_ae
  have h1 : ∀ᵐ u ∂(volume.restrict (Icc (ccdf μ w') (ccdf μ w))), u ∈ Icc (ccdf μ w') (ccdf μ w) :=
    ae_restrict_mem measurableSet_Icc
  have h2 : ∀ᵐ u ∂(volume.restrict (Icc (ccdf μ w') (ccdf μ w))), u ∉ ({ccdf μ w} : Set ℝ) :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton)
  filter_upwards [h1, h2] with u hu hne
  simp only [mem_singleton_iff] at hne
  have hult : u < ccdf μ w := lt_of_le_of_ne hu.2 hne
  have hs := (Q_mem μ hac hww'.le u).1
  have hFs := ccdf_Q μ hac hww'.le hu.1 hu.2
  set s := Q μ w w' u with hsdef
  have hs0 : 0 ≤ s := le_trans hw hs.1
  have hw'0 : 0 ≤ w' := by linarith
  set x := minGenInv w' Hu u with hxdef
  have hbdd : BddBelow (insert w' {y : ℝ | 0 ≤ y ∧ Hu y ≤ u}) := by
    refine ⟨0, fun y hy => ?_⟩
    rcases hy with rfl | hy
    · exact hw'0
    · exact hy.1
  have hx_le : x ≤ w' := csInf_le hbdd (mem_insert _ _)
  have hx_ge : s ≤ x := by
    refine le_csInf (insert_nonempty _ _) ?_
    intro y hy
    rcases hy with rfl | hy
    · exact hs.2
    · by_cases hyw : y < w
      · have := hHu_anti (mem_Ici.mpr hy.1) (mem_Ici.mpr hw) hyw.le
        rw [hHu_w] at this
        linarith [hy.2]
      · push Not at hyw
        by_cases hyw' : y ≤ w'
        · exact (Q_le_iff μ hac hww'.le hu.1 ⟨hyw, hyw'⟩).mpr
            (le_trans (hHu y ⟨hyw, hyw'⟩) hy.2)
        · push Not at hyw'
          exact le_trans hs.2 hyw'.le
  have hgu : 0 ≤ g u := hg u ⟨le_trans (ccdf_nonneg μ _) hu.1, le_trans hu.2 (ccdf_le_one μ _)⟩
  have hgx : γ * x ∈ Icc (γ * w) (γ * w') :=
    ⟨mul_le_mul_of_nonneg_left (le_trans hs.1 hx_ge) hγ.le, mul_le_mul_of_nonneg_left hx_le hγ.le⟩
  have hgs : γ * s ∈ Icc (γ * w) (γ * w') :=
    ⟨mul_le_mul_of_nonneg_left hs.1 hγ.le, mul_le_mul_of_nonneg_left hs.2 hγ.le⟩
  have hs0' : 0 ≤ γ * s := mul_nonneg hγ.le hs0
  have k1 : γ * x * Hl (γ * x) ≤ γ * s * Hl (γ * s) :=
    hvHl hgs hgx (mul_le_mul_of_nonneg_left hx_ge hγ.le)
  have k2 : γ * s * Hl (γ * s) ≤ γ * s * ccdf μ (γ * s) :=
    mul_le_mul_of_nonneg_left (hHl _ hgs) hs0'
  show ENNReal.ofReal (γ * x * Hl (γ * x) * g u) ≤
    ENNReal.ofReal (γ * s * ccdf μ (γ * s) * g (ccdf μ s))
  rw [hFs]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (le_trans k1 k2) hgu
