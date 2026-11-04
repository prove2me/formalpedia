-- Prove2me | solution 1 for ThreeSum.LightPrimePool.prefix_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:46.475804+00:00
-- url     : https://prove2.me/submissions/a5f8e704-ef3d-42d8-bf2a-821b459ab547

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_WeightedCache3SUM_Alias_ec6abe6e008eb668

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution (y i : ℕ) : (scanned y i).Nodup :=
  (prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)
end ThreeSum.LightPrimePool
