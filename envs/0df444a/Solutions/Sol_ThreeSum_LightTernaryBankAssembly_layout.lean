-- Prove2me | solution 1 for ThreeSum.LightTernaryBankAssembly.layout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:48.901236+00:00
-- url     : https://prove2.me/submissions/f0593284-678f-47dc-bba8-a8768d96090c

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
namespace ThreeSum.LightTernaryBankAssembly
theorem _root_.solution (a n N : ℕ) :
    a+n≤keyBase a n ∧ keyBase a n+4*n≤powersBase a n ∧
    powersBase a n+(2*N+1)≤fBase a n N ∧
    fBase a n N+(N+1)*n≤gBase a n N ∧
    gBase a n N+(N+1)*n≤hBase a n N ∧
    hBase a n N+(N+1)*n≤space a n N := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩
end ThreeSum.LightTernaryBankAssembly
