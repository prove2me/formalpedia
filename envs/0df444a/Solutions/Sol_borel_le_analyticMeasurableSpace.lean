-- Prove2me | solution 1 for borel_le_analyticMeasurableSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:37.805554+00:00
-- url     : https://prove2.me/submissions/fa815615-baac-4bf1-9527-3965d6680d52

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Theorems.Thm_MeasureTheory_AnalyticSet_mem_analyticMeasurableSpace

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] :
    ‹MeasurableSpace X› ≤ analyticMeasurableSpace X :=
  fun _ hs => hs.analyticSet.mem_analyticMeasurableSpace
