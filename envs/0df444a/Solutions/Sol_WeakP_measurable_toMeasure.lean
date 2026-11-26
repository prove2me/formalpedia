-- Prove2me | solution 1 for WeakP.measurable_toMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:14.744196+00:00
-- url     : https://prove2.me/submissions/c2045b89-9370-4cb6-b6a8-671d547456e1

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
import Theorems.Thm_probabilityMeasure_borel_measurable_toMeasure


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open WeakP
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W]
  [OpensMeasurableSpace W]
namespace WeakP
theorem _root_.solution [PolishSpace W] [BorelSpace W] :
    Measurable (toMeasure : WeakP W → Measure W) := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable W
  exact probabilityMeasure_borel_measurable_toMeasure (Ω := W)
end WeakP
