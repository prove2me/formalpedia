-- Prove2me | solution 1 for Sqrt6KissingBound.standardBicone_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:25.978268+00:00
-- url     : https://prove2.me/submissions/1939d2f7-8f59-4adb-a898-e524f74e3634

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset
import Theorems.Thm_Sqrt6KissingBound_upperBicone_subset

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) :
    standardBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  exact union_subset (lowerBicone_subset k) (upperBicone_subset k)
end Sqrt6KissingBound
