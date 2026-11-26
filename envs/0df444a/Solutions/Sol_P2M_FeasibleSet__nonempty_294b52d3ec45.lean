-- Prove2me | solution 1 for P2M_FeasibleSet__nonempty_294b52d3ec45
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:11.449111+00:00
-- url     : https://prove2.me/submissions/99ca6814-aebc-4eec-9357-707b5ed88986

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_MeasureTheory_Measure_map_fst_prod_of_isProbabilityMeasure
import Theorems.Thm_MeasureTheory_Measure_map_snd_prod_of_isProbabilityMeasure

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
omit [MeasurableSpace X₀] [MeasurableSpace Y₀]
namespace FeasibleSet₀
theorem _root_.solution
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y))
    (z₀ : X₀ × Y₀) :
    (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty := by
  haveI := hκμ z₀.1
  haveI := hκν z₀.2
  exact ⟨(κ_μ z₀.1).prod (κ_ν z₀.2),
    Measure.map_fst_prod_of_isProbabilityMeasure _ _,
    Measure.map_snd_prod_of_isProbabilityMeasure _ _⟩
end FeasibleSet₀
