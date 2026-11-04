-- Prove2me | solution 1 for ThreeSum.ModuloCosts.log_le_roundedPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:34.153204+00:00
-- url     : https://prove2.me/submissions/1ba4b4f6-0e65-41cd-8efa-e676ee8b9327

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Theorems.Thm_ThreeSum_ModuloCosts_capacity_le_roundedPower

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCosts
open KaratsubaInterface
namespace ThreeSum.ModuloCosts
theorem _root_.solution (p : ℕ) : Nat.clog 2 p ≤ roundedPower p :=
  (Nat.lt_pow_self (by decide : 1 < 2)).le.trans (capacity_le_roundedPower p)
end ThreeSum.ModuloCosts
