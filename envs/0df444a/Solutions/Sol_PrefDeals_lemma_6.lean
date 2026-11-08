-- Prove2me | solution 1 for PrefDeals.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:12:59.155885+00:00
-- url     : https://prove2.me/submissions/65c822f2-1644-407a-9bc6-e54566cbefc4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PrefDeals.Aux_PD

theorem Iic_le {μF μG : Measure ℝ} [IsProbabilityMeasure μF] [IsProbabilityMeasure μG]
    (hFG : ∀ x, cdf μG x ≤ cdf μF x) (a : ℝ) : μG (Set.Iic a) ≤ μF (Set.Iic a) := by
  rw [← ofReal_cdf, ← ofReal_cdf]
  exact ENNReal.ofReal_le_ofReal (hFG a)

theorem Iio_le {μF μG : Measure ℝ} [IsProbabilityMeasure μF] [IsProbabilityMeasure μG]
    (hFG : ∀ x, cdf μG x ≤ cdf μF x) (a : ℝ) : μG (Set.Iio a) ≤ μF (Set.Iio a) := by
  have hU : Set.Iio a = ⋃ n : ℕ, Set.Iic (a - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ => Set.Iic (a - 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply Set.Iic_subset_Iic.mpr
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rw [hU, hmono.measure_iUnion, hmono.measure_iUnion]
  exact iSup_mono fun n => Iic_le hFG _

theorem upper_le {μF μG : Measure ℝ} [IsProbabilityMeasure μF] [IsProbabilityMeasure μG]
    (hFG : ∀ x, cdf μG x ≤ cdf μF x) (U : Set ℝ) (hU : IsUpperSet U) :
    μF U ≤ μG U := by
  rcases U.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  by_cases hbdd : BddBelow U
  · set a := sInf U with ha
    have hsub : U ⊆ Set.Ici a := fun x hx => csInf_le hbdd hx
    have hIoi : Set.Ioi a ⊆ U := by
      intro x hx
      obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hne hx
      exact hU hux.le hu
    by_cases haU : a ∈ U
    · have : U = Set.Ici a := by
        apply le_antisymm hsub
        intro x hx
        exact hU hx haU
      rw [this, ← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
        prob_compl_eq_one_sub measurableSet_Iio]
      exact tsub_le_tsub_left (Iio_le hFG a) 1
    · have : U = Set.Ioi a := by
        apply le_antisymm _ hIoi
        intro x hx
        rcases (Set.mem_Ici.mp (hsub hx)).lt_or_eq with h | h
        · exact h
        · exact absurd (by rw [h]; exact hx) haU
      rw [this, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
        prob_compl_eq_one_sub measurableSet_Iic]
      exact tsub_le_tsub_left (Iic_le hFG a) 1
  · have : U = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      rw [not_bddBelow_iff] at hbdd
      obtain ⟨u, hu, hux⟩ := hbdd x
      exact hU hux.le hu
    rw [this]; simp

end PrefDeals.Aux_PD

open PrefDeals.Aux_PD in
theorem solution (φ : ℝ → ℝ) (hφ : Monotone φ) (μF μG : Measure ℝ)
    [IsProbabilityMeasure μF] [IsProbabilityMeasure μG]
    (hFG : ∀ x, cdf μG x ≤ cdf μF x)
    (hiF : Integrable φ μF) (hiG : Integrable φ μG) :
    ∫ x, φ x ∂μF ≤ ∫ x, φ x ∂μG := by
  have hmeas : Measurable φ := hφ.measurable
  set fp : ℝ → ℝ := fun x => max (φ x) 0 with hfp
  set fn : ℝ → ℝ := fun x => max (-φ x) 0 with hfn
  have hfp_mono : Monotone fp := fun a b h => max_le_max (hφ h) le_rfl
  have hfn_anti : Antitone fn := fun a b h => max_le_max (neg_le_neg (hφ h)) le_rfl
  have hfpm : Measurable fp := hmeas.max measurable_const
  have hfnm : Measurable fn := hmeas.neg.max measurable_const
  have hsplit : ∀ x, φ x = fp x - fn x := by
    intro x
    show φ x = max (φ x) 0 - max (-φ x) 0
    rcases le_total 0 (φ x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hint : ∀ μ : Measure ℝ, Integrable φ μ → ∫ x, φ x ∂μ = ∫ x, fp x ∂μ - ∫ x, fn x ∂μ := by
    intro μ hi
    have hfpi : Integrable fp μ := hi.sup (integrable_zero _ _ _)
    have hfni : Integrable fn μ := hi.neg.sup (integrable_zero _ _ _)
    rw [← integral_sub hfpi hfni]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => hsplit x
  -- layer cake comparisons
  have hpos : ∫⁻ x, ENNReal.ofReal (fp x) ∂μF ≤ ∫⁻ x, ENNReal.ofReal (fp x) ∂μG := by
    rw [lintegral_eq_lintegral_meas_lt μF (f := fp) (Filter.Eventually.of_forall fun x => le_max_right _ _)
        hfpm.aemeasurable,
      lintegral_eq_lintegral_meas_lt μG (f := fp) (Filter.Eventually.of_forall fun x => le_max_right _ _)
        hfpm.aemeasurable]
    apply lintegral_mono
    intro t
    apply upper_le hFG
    intro a b hab ha
    exact lt_of_lt_of_le ha (hfp_mono hab)
  have hneg : ∫⁻ x, ENNReal.ofReal (fn x) ∂μG ≤ ∫⁻ x, ENNReal.ofReal (fn x) ∂μF := by
    rw [lintegral_eq_lintegral_meas_lt μF (f := fn) (Filter.Eventually.of_forall fun x => le_max_right _ _)
        hfnm.aemeasurable,
      lintegral_eq_lintegral_meas_lt μG (f := fn) (Filter.Eventually.of_forall fun x => le_max_right _ _)
        hfnm.aemeasurable]
    apply lintegral_mono
    intro t
    have hU : IsUpperSet {a : ℝ | t < fn a}ᶜ := by
      intro a b hab ha
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at ha ⊢
      exact le_trans (hfn_anti hab) ha
    have hmeasS : MeasurableSet {a : ℝ | t < fn a} := measurableSet_lt measurable_const hfnm
    have := upper_le hFG _ hU
    rw [prob_compl_eq_one_sub hmeasS, prob_compl_eq_one_sub hmeasS] at this
    have hF1 : μF {a : ℝ | t < fn a} ≤ 1 := prob_le_one
    have hG1 : μG {a : ℝ | t < fn a} ≤ 1 := prob_le_one
    exact (ENNReal.sub_le_sub_iff_left hG1 ENNReal.one_ne_top).mp this
  have hfpF : ∫ x, fp x ∂μF = (∫⁻ x, ENNReal.ofReal (fp x) ∂μF).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => le_max_right _ _)
      hfpm.aestronglyMeasurable
  have hfpG : ∫ x, fp x ∂μG = (∫⁻ x, ENNReal.ofReal (fp x) ∂μG).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => le_max_right _ _)
      hfpm.aestronglyMeasurable
  have hfnF : ∫ x, fn x ∂μF = (∫⁻ x, ENNReal.ofReal (fn x) ∂μF).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => le_max_right _ _)
      hfnm.aestronglyMeasurable
  have hfnG : ∫ x, fn x ∂μG = (∫⁻ x, ENNReal.ofReal (fn x) ∂μG).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => le_max_right _ _)
      hfnm.aestronglyMeasurable
  have hfinG : ∫⁻ x, ENNReal.ofReal (fp x) ∂μG ≠ ⊤ :=
    (hiG.sup (integrable_zero _ _ _)).lintegral_lt_top.ne
  have hfinF : ∫⁻ x, ENNReal.ofReal (fn x) ∂μF ≠ ⊤ :=
    (hiF.neg.sup (integrable_zero _ _ _)).lintegral_lt_top.ne
  rw [hint μF hiF, hint μG hiG, hfpF, hfpG, hfnF, hfnG]
  have h1 := ENNReal.toReal_mono hfinG hpos
  have h2 := ENNReal.toReal_mono hfinF hneg
  linarith
