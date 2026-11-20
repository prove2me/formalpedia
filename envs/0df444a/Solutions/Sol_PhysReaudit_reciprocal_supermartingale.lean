-- Prove2me | solution 1 for PhysReaudit.reciprocal_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:51:43.624229+00:00
-- url     : https://prove2.me/submissions/a789b990-aefc-4a9e-bc8f-86d3f6febd51

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory ProbabilityTheory PhysReaudit

theorem solution {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) {q : ℝ}
    (hq : q ∈ Set.Icc 0 q₀) :
    q * (t / q₀) + (1 - q) * ((1 - t) / (1 - q₀)) ≤ 1 ∧
    (∀ n y, 0 ≤ Real.exp (-sprtS q₀ t y n)) ∧
    Supermartingale (fun n y => Real.exp (-sprtS q₀ t y n)) pastFiltration
      (Measure.infinitePi fun _ : ℕ => bern q) := by
  obtain ⟨hq0, hqq⟩ := hq
  have ht0 : 0 < t := h0.trans h1
  have h1q0 : 0 < 1 - q₀ := by linarith
  have hfirst : q * (t / q₀) + (1 - q) * ((1 - t) / (1 - q₀)) ≤ 1 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have e : q * (t * q₀⁻¹) + (1 - q) * ((1 - t) * (1 - q₀)⁻¹)
        = 1 - (q₀ - q) * (t * q₀⁻¹ - (1 - t) * (1 - q₀)⁻¹) := by
      field_simp; ring
    rw [e]
    have hs : 0 ≤ t * q₀⁻¹ - (1 - t) * (1 - q₀)⁻¹ := by
      rw [sub_nonneg, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ h1q0 h0]; nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hqq) hs]
  refine ⟨hfirst, fun n y => (Real.exp_pos _).le, ?_⟩
  haveI hb : IsProbabilityMeasure (bern q) := by
    constructor
    simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hq0 (by linarith)]; simp
  set μ := Measure.infinitePi fun _ : ℕ => bern q with hμ
  set h : Bool → ℝ := fun b => Real.exp (-sprtIncr q₀ t b) with hh
  set C := |zMinus q₀ t| + |zPlus q₀ t| with hC
  have hincr : ∀ b, |sprtIncr q₀ t b| ≤ C := by
    intro b; cases b <;> simp [sprtIncr, hC]
  -- measurability of the walk at time n for the past filtration
  have hcoord : ∀ n i, i < n → Measurable[pastFiltration n] (fun y : ℕ → Bool => y i) := by
    intro n i hi
    refine Measurable.mono (comap_measurable _) ?_ le_rfl
    exact le_iSup₂ (f := fun j (_ : j ∈ Finset.range n) =>
      MeasurableSpace.comap (fun y : ℕ → Bool => y j) inferInstance) i (Finset.mem_range.mpr hi)
  have hSm : ∀ n, Measurable[pastFiltration n] (fun y => sprtS q₀ t y n) := by
    intro n
    unfold sprtS
    refine Finset.measurable_sum _ (fun i hi => ?_)
    exact (measurable_of_countable (sprtIncr q₀ t)).comp (hcoord n i (Finset.mem_range.mp hi))
  have hfm : ∀ n, Measurable[pastFiltration n] (fun y => Real.exp (-sprtS q₀ t y n)) :=
    fun n => (hSm n).neg.exp
  have hbound : ∀ n y, |sprtS q₀ t y n| ≤ n * C := by
    intro n y
    unfold sprtS
    calc |∑ i ∈ Finset.range n, sprtIncr q₀ t (y i)| ≤ ∑ i ∈ Finset.range n, |sprtIncr q₀ t (y i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, C := Finset.sum_le_sum (fun i _ => hincr _)
      _ = n * C := by simp
  have hint : ∀ n, Integrable (fun y => Real.exp (-sprtS q₀ t y n)) μ := by
    intro n
    refine Integrable.of_bound (C := Real.exp (n * C)) ((hfm n).mono ((pastFiltration).le n) le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by have hb := hbound n y; have := neg_le_abs (sprtS q₀ t y n); linarith)
  refine supermartingale_nat (fun n => (hfm n).stronglyMeasurable) hint (fun n => ?_)
  -- one step
  have hsplit : (fun y : ℕ → Bool => Real.exp (-sprtS q₀ t y (n + 1)))
      = (fun y => Real.exp (-sprtS q₀ t y n)) * (fun y => h (y n)) := by
    funext y
    simp only [Pi.mul_apply, hh, sprtS, Finset.sum_range_succ, neg_add, Real.exp_add]
  have hgm : Measurable (fun y : ℕ → Bool => h (y n)) :=
    (measurable_of_countable h).comp (measurable_pi_apply n)
  have hgint : Integrable (fun y : ℕ → Bool => h (y n)) μ := by
    refine Integrable.of_bound (C := Real.exp C) hgm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by have hb := hincr (y n); have := neg_le_abs (sprtIncr q₀ t (y n)); linarith)
  have hprod_int : Integrable ((fun y => Real.exp (-sprtS q₀ t y n)) * (fun y => h (y n))) μ := by
    rw [← hsplit]; exact hint (n + 1)
  rw [hsplit]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := pastFiltration n) (hfm n).stronglyMeasurable
    hprod_int hgint
  -- conditional expectation of the fresh factor is its mean
  have hind : iIndepFun (fun i (ω : ℕ → Bool) => ω i) μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => bern q) (X := fun _ b => b) (fun _ => measurable_id)
  have hI : Indep (⨆ i ∈ ({n} : Set ℕ), MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance)
      (⨆ i ∈ ((Finset.range n : Finset ℕ) : Set ℕ),
        MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance) μ :=
    indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind (by simp)
  simp only [iSup_singleton] at hI
  have hgm' : StronglyMeasurable[MeasurableSpace.comap (fun ω : ℕ → Bool => ω n) inferInstance]
      (fun y : ℕ → Bool => h (y n)) :=
    ((measurable_of_countable h).comp (comap_measurable _)).stronglyMeasurable
  have hce := condExp_indep_eq (measurable_pi_apply n).comap_le ((pastFiltration).le n) hgm' hI
  have hmean : ∫ y, h (y n) ∂μ = q * (t / q₀) + (1 - q) * ((1 - t) / (1 - q₀)) := by
    have hmap : ∫ y, h (y n) ∂μ = ∫ b, h b ∂(bern q) := by
      rw [← (measurePreserving_eval_infinitePi (fun _ : ℕ => bern q) n).map_eq,
        integral_map (measurable_pi_apply n).aemeasurable (measurable_of_countable h).aestronglyMeasurable]
    rw [hmap]
    have i1 : Integrable h (Measure.dirac true) := integrable_dirac (by simp)
    have i0 : Integrable h (Measure.dirac false) := integrable_dirac (by simp)
    rw [bern, integral_add_measure (i1.smul_measure ENNReal.ofReal_ne_top)
      (i0.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (by linarith)]
    simp only [hh, sprtIncr, zMinus, zPlus, if_true, Bool.false_eq_true, if_false, smul_eq_mul,
      Real.exp_neg]
    rw [Real.exp_log (div_pos h0 ht0), Real.exp_log (div_pos h1q0 (by linarith)), inv_div, inv_div]
  filter_upwards [hpull, hce] with y hy hy2
  rw [hy, Pi.mul_apply, hy2, hmean]
  exact mul_le_of_le_one_right (Real.exp_pos _).le hfirst
