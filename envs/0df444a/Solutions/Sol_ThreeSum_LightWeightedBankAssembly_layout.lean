-- Prove2me | solution 1 for ThreeSum.LightWeightedBankAssembly.layout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:20.417758+00:00
-- url     : https://prove2.me/submissions/219fcaf0-804c-403e-8d3e-1a0f294c0038

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
namespace ThreeSum.LightWeightedBankAssembly
theorem _root_.solution (a n N : ℕ) :
    a+n≤keyBase a n ∧ keyBase a n+4*n≤powersBase a n ∧
    powersBase a n+(2*N+1)≤fBase a n N ∧
    fBase a n N+(N+1)*n≤gBase a n N ∧
    gBase a n N+(N+1)*n≤hBase a n N ∧
    hBase a n N+(N+1)*n≤space a n N := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩
end ThreeSum.LightWeightedBankAssembly
