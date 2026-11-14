-- Prove2me | solution 1 for avram_chat24_physical_cell_volume_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:15:34.201818+00:00
-- url     : https://prove2.me/submissions/ab6b929c-8266-4244-a66b-8bc638322439

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution (T : ℝ) (s t : ℝ≥0)
    (hst : s ≤ t) (htT : (t : ℝ) ≤ T) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    μ (Ioc s t) = ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by
  have hpre : Real.toNNReal ⁻¹' (Ioc s t) ∩ Icc (0 : ℝ) T =
      Ioc (s : ℝ) (t : ℝ) := by
    ext r
    constructor
    · rintro ⟨hr, hr0, hrT⟩
      have he : (Real.toNNReal r : ℝ) = r := Real.coe_toNNReal r hr0
      change (s : ℝ) < (Real.toNNReal r : ℝ) ∧
        (Real.toNNReal r : ℝ) ≤ (t : ℝ) at hr
      change (s : ℝ) < r ∧ r ≤ (t : ℝ)
      simpa only [he] using hr
    · rintro ⟨hs, ht⟩
      have hr0 : 0 ≤ r := le_trans s.property hs.le
      have he : (Real.toNNReal r : ℝ) = r := Real.coe_toNNReal r hr0
      refine ⟨?_, hr0, ht.trans htT⟩
      change (s : ℝ) < (Real.toNNReal r : ℝ) ∧
        (Real.toNNReal r : ℝ) ≤ (t : ℝ)
      simpa only [he] using And.intro hs ht
  change (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) (Ioc s t) = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioc,
    Measure.restrict_apply (measurableSet_Ioc.preimage (by fun_prop)),
    hpre, Real.volume_Ioc]
