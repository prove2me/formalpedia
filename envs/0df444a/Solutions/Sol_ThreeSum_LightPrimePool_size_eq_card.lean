-- Prove2me | solution 1 for ThreeSum.LightPrimePool.size_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:02:02.842062+00:00
-- url     : https://prove2.me/submissions/09550b58-104c-4977-b13e-cae63e79e241

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_values_nodup
import Theorems.Thm_ThreeSum_LightPrimePool_values_toFinset

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution (y : ℕ) : size y = (PrimeDensity.candidates y).card := by
  rw [← values_toFinset,List.toFinset_card_of_nodup (values_nodup y)]
  rfl
end ThreeSum.LightPrimePool
