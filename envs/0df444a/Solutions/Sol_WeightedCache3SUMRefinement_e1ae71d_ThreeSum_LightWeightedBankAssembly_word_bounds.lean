-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.word_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:14:24.100621+00:00
-- url     : https://prove2.me/submissions/c01cc932-798f-4af3-bac6-014de5ec91f2

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
theorem _root_.solution (a n N V : ℕ) :
    space a n N≤word a n N V ∧ n+2^(2*N+1)+16≤word a n N V ∧
    2*N+3≤word a n N V ∧ 4*(4^N*V)+3≤word a n N V ∧
    valueBound N V≤word a n N V ∧ 4*(4^N*valueBound N V)+3≤word a n N V := by
  unfold word
  generalize 2^(2*N+1)=p
  generalize 4^N=q
  generalize valueBound N V=b
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
