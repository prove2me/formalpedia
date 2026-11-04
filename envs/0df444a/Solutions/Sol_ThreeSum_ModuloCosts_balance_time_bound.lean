-- Prove2me | solution 1 for ThreeSum.ModuloCosts.balance_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:54.794491+00:00
-- url     : https://prove2.me/submissions/72c78ccc-e19c-4bec-a69b-056080faf927

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_WeightedCache3SUM_Alias_f1c95625e9077016
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_KaratsubaInterface_time_with_linear_bound
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCosts
open KaratsubaInterface
namespace ThreeSum.ModuloCosts
theorem _root_.solution (p : ℕ) :
    LightBalancedOffset.time (Nat.clog 2 p) p ≤ 2982*roundedPower p := by
  exact (LightBalancedOffset.time_bound _ _ (le_capacity p)).trans
    (time_with_linear_bound (Nat.clog 2 p) 226)
end ThreeSum.ModuloCosts
