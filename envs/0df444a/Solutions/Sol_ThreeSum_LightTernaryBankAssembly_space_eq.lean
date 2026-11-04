-- Prove2me | solution 1 for ThreeSum.LightTernaryBankAssembly.space_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:06.522268+00:00
-- url     : https://prove2.me/submissions/a353d050-a765-4a10-a766-136d52506401

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
namespace ThreeSum.LightTernaryBankAssembly
theorem _root_.solution (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by
  unfold space hBase gBase fBase powersBase keyBase
  ring
end ThreeSum.LightTernaryBankAssembly
