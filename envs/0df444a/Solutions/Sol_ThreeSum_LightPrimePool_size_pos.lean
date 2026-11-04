-- Prove2me | solution 1 for ThreeSum.LightPrimePool.size_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:01.617409+00:00
-- url     : https://prove2.me/submissions/9584a9f6-9b5f-4ef8-b0d3-4cf45e7e3ae9

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_values_nonempty

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y : ℕ} (hy : 0 < y) : 0 < size y :=
  List.length_pos_iff.mpr (values_nonempty hy)
end ThreeSum.LightPrimePool
