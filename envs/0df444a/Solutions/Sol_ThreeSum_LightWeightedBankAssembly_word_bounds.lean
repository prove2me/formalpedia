-- Prove2me | solution 1 for ThreeSum.LightWeightedBankAssembly.word_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:36.280649+00:00
-- url     : https://prove2.me/submissions/a55900df-7026-4e96-b70d-b60c04e5004a

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
namespace ThreeSum.LightWeightedBankAssembly
theorem _root_.solution (a n N V : ℕ) :
    space a n N≤word a n N V ∧ n+2^(2*N+1)+16≤word a n N V ∧
    2*N+3≤word a n N V ∧ 4*(4^N*V)+3≤word a n N V ∧
    valueBound N V≤word a n N V ∧ 4*(4^N*valueBound N V)+3≤word a n N V := by
  unfold word
  generalize 2^(2*N+1)=p
  generalize 4^N=q
  generalize valueBound N V=b
  omega
end ThreeSum.LightWeightedBankAssembly
