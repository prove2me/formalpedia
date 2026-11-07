-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_zone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:52.748632+00:00
-- url     : https://prove2.me/submissions/0282fa79-b10d-4032-b9df-bf311d49cefd

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (a b : ℝ) : MeasurableSet (zone u a b) := by
  change MeasurableSet ({s : Sphere | a ≤ inner ℝ (u : Space) (s : Space)} ∩
    {s : Sphere | inner ℝ (u : Space) (s : Space) ≤ b})
  exact (measurableSet_cap u a).inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap
