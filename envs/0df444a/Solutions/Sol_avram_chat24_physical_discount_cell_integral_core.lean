-- Prove2me | solution 1 for avram_chat24_physical_discount_cell_integral_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:04.623937+00:00
-- url     : https://prove2.me/submissions/6a179e6b-f006-4efd-89c0-28eafcd047d9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution (q T : ℝ) (hT : 0 ≤ T)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : (t : ℝ) ≤ T) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    (∫ r in Ioc s t, Real.exp (-(q * (r : ℝ))) * (-q) ∂μ) =
      Real.exp (-(q * (t : ℝ))) - Real.exp (-(q * (s : ℝ))) := by
  classical
  intro μ
  let k : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ))) * (-q)
  let g : ℝ → ℝ := fun r => Real.exp (-(q * r)) * (-q)
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hm : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  have hfm : AEStronglyMeasurable ((Ioc s t).indicator k) μ :=
    hk.aestronglyMeasurable.indicator measurableSet_Ioc
  have hsub : Ioc (s : ℝ) (t : ℝ) ⊆ Icc (0 : ℝ) T := by
    intro r hr
    exact ⟨s.property.trans hr.1.le, hr.2.trans htT⟩
  have hderiv (r : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-(q * y)))
      (g r) r := by
    simpa only [g, id_eq, neg_mul, mul_one] using (HasDerivAt.const_mul (-q) (hasDerivAt_id r)).exp
  change (∫ r in Ioc s t, k r ∂μ) = _
  calc
    (∫ r in Ioc s t, k r ∂μ) = ∫ r, (Ioc s t).indicator k r ∂μ :=
      (integral_indicator measurableSet_Ioc).symm
    _ = ∫ r, (Ioc s t).indicator k (Real.toNNReal r)
        ∂((volume : Measure ℝ).restrict (Icc 0 T)) :=
      integral_map hm.aemeasurable hfm
    _ = ∫ r, (Ioc (s : ℝ) (t : ℝ)).indicator g r
        ∂((volume : Measure ℝ).restrict (Icc 0 T)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      simp only [Set.indicator, Set.mem_Ioc, k, g, ← NNReal.coe_lt_coe,
        ← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hr.1, NNReal.coe_mk]
    _ = ∫ r in Ioc (s : ℝ) (t : ℝ), g r := by
      rw [integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub]
    _ = ∫ r in (s : ℝ)..(t : ℝ), g r :=
      (intervalIntegral.integral_of_le (by exact_mod_cast hst)).symm
    _ = Real.exp (-(q * (t : ℝ))) - Real.exp (-(q * (s : ℝ))) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r)
        (hg.intervalIntegrable _ _)
end
