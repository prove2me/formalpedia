-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.space_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:14:31.807946+00:00
-- url     : https://prove2.me/submissions/190039b6-d7f9-4909-9b4f-ea37ada7d462

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
theorem _root_.solution (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by
  unfold space hBase gBase fBase powersBase keyBase
  ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
