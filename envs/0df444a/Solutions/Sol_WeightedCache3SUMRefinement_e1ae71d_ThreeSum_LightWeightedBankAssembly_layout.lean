-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.layout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:14:19.821922+00:00
-- url     : https://prove2.me/submissions/e73f9564-518f-4d5e-be9d-8ff67823dd1a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
theorem _root_.solution (a n N : ℕ) :
    a+n≤keyBase a n ∧ keyBase a n+4*n≤powersBase a n ∧
    powersBase a n+(2*N+1)≤fBase a n N ∧
    fBase a n N+(N+1)*n≤gBase a n N ∧
    gBase a n N+(N+1)*n≤hBase a n N ∧
    hBase a n N+(N+1)*n≤space a n N := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly
