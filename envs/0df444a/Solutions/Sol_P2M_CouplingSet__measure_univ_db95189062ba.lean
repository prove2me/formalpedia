-- Prove2me | solution 1 for P2M_CouplingSet__measure_univ_db95189062ba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:28.770524+00:00
-- url     : https://prove2.me/submissions/8fdd8837-fccd-464b-a7cc-46edf1d4e28c

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_MultiPeriod_Feas_measure_univ


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
namespace CouplingSet₀
theorem _root_.solution
    {μ₀ : Measure X₀} {ν₀ : Measure Y₀} [hμ₀ : IsProbabilityMeasure μ₀]
    {γ₀ : Measure (X₀ × Y₀)} (hγ₀ : γ₀ ∈ CouplingSet₀ μ₀ ν₀) :
    γ₀ Set.univ = 1 := by
  have h1 : (γ₀.map Prod.fst) Set.univ = 1 := by
    rw [hγ₀.1]; exact hμ₀.measure_univ
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] at h1
end CouplingSet₀
