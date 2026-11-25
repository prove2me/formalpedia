-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_assoc_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:15.351505+00:00
-- url     : https://prove2.me/submissions/0015d9bc-b6c5-46bf-bbb6-ea62d5793bef

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactRest_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Theorems.Thm_Bl_general_b_fact_rest_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) :
    ∃ q ∈ associatedPrimes R (QuotSMulTop x M), p < q ∧ x ∈ q ∧ x ∉ p := by
  first | exact Bl.general_b_fact_rest.goal1 .. | (apply Bl.general_b_fact_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_rest.goal1 <;> assumption)
end ReciprocityTheory.CA
