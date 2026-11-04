-- Prove2me | solution 1 for ThreeSum.LightWeightedBankAssembly.space_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:35.084358+00:00
-- url     : https://prove2.me/submissions/200ad58b-8d76-462f-a05d-37186d13d01b

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
namespace ThreeSum.LightWeightedBankAssembly
theorem _root_.solution (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by
  unfold space hBase gBase fBase powersBase keyBase
  ring
end ThreeSum.LightWeightedBankAssembly
