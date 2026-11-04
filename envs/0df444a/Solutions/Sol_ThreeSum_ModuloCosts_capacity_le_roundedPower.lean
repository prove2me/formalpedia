-- Prove2me | solution 1 for ThreeSum.ModuloCosts.capacity_le_roundedPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:53.884644+00:00
-- url     : https://prove2.me/submissions/f376a6a8-ddd1-4028-8737-6cf9acb88dee

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_ModuloCosts

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCosts
open KaratsubaInterface
namespace ThreeSum.ModuloCosts
theorem _root_.solution (p : ℕ) : capacity p ≤ roundedPower p :=
  Nat.pow_le_pow_left (by decide) _
end ThreeSum.ModuloCosts
