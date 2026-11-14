-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.ordered_excess_measure_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:17:36.345894+00:00
-- url     : https://prove2.me/submissions/3267d159-b02e-478c-8cf6-425749b0c6fd

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

private theorem coupling_marginals {X : Type} [MeasurableSpace X] (common low high : Measure X)
    [IsFiniteMeasure common] [IsFiniteMeasure low] [IsFiniteMeasure high]
    (hmass : low univ = high univ) (h0 : low univ ≠ 0) :
    let π : Measure (X × X) := Measure.map (fun x => (x,x)) common +
      (low univ)⁻¹ • (low.prod high)
    Measure.map Prod.fst π = common+low ∧ Measure.map Prod.snd π = common+high := by
  classical
  have hf : Measurable (fun x : X => (x,x)) := measurable_id.prodMk measurable_id
  have hfin : low univ ≠ ∞ := measure_ne_top _ _
  have hc : (low univ)⁻¹ * low univ = 1 := ENNReal.inv_mul_cancel h0 hfin
  constructor
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_map measurable_fst hf,
      Measure.map_fst_prod]
    simp only [Function.comp_def, Measure.map_id, ← hmass, smul_smul, hc, one_smul]
    change Measure.map id common + low = common + low
    rw [Measure.map_id]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_map measurable_snd hf,
      Measure.map_snd_prod]
    simp only [Function.comp_def, Measure.map_id, smul_smul, hc, one_smul]
    change Measure.map id common + high = common + high
    rw [Measure.map_id]

theorem solution (common low high : Measure ℝ)
    [IsFiniteMeasure common] [IsFiniteMeasure low] [IsFiniteMeasure high]
    (hmass : low univ = high univ) (h0 : low univ ≠ 0) (t : ℝ)
    (hlow : ∀ᵐ x ∂low, x ≤ t) (hhigh : ∀ᵐ y ∂high, t ≤ y) :
    let π : Measure (ℝ × ℝ) := Measure.map (fun x => (x,x)) common +
      (low univ)⁻¹ • (low.prod high)
    Measure.map Prod.fst π = common+low ∧ Measure.map Prod.snd π = common+high ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) := by
  have hm := coupling_marginals common low high hmass h0
  refine ⟨hm.1,hm.2,?_⟩
  have hdiag : ∀ᵐ p ∂(Measure.map (fun x : ℝ => (x,x)) common), p.1 ≤ p.2 := by
    apply (ae_map_iff (measurable_id.prodMk measurable_id).aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).2
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  have hprod : ∀ᵐ p ∂(low.prod high), p.1 ≤ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_fst measurable_snd)).2
    filter_upwards [hlow] with x hx
    filter_upwards [hhigh] with y hy
    exact hx.trans hy
  have hscale := Measure.ae_smul_measure hprod ((low univ)⁻¹)
  apply ae_iff.mpr
  rw [Measure.add_apply,ae_iff.mp hdiag,ae_iff.mp hscale,add_zero]
