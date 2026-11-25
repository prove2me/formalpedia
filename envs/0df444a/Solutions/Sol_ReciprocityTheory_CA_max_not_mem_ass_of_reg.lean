-- Prove2me | solution 1 for ReciprocityTheory.CA.max_not_mem_ass_of_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:40.318991+00:00
-- url     : https://prove2.me/submissions/7603a1a4-4286-4c1a-afa7-f34801e3c942

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_ReciprocityTheory_CA_socle_of_max_mem_ass

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
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N] {w : R}
    (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular N w) :
    maximalIdeal R ∉ associatedPrimes R N := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  exact ha (rw (show w • a = w • (0 : N) by rw [hz w hw, smul_zero]))
end ReciprocityTheory.CA
