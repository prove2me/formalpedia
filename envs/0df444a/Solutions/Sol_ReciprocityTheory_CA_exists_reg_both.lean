-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_reg_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:36.992867+00:00
-- url     : https://prove2.me/submissions/c1cea4ee-1609-4db9-8204-84888dae5cd1

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_Bl_general_b_fact_side_goal1


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
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : maximalIdeal R ∉ associatedPrimes R N₁) (h₂ : maximalIdeal R ∉ associatedPrimes R N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  first | exact Bl.general_b_fact_side.goal1 .. | (apply Bl.general_b_fact_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_side.goal1 <;> assumption)
end ReciprocityTheory.CA
