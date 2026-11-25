-- Prove2me | solution 1 for ReciprocityTheory.CA.ModDepthGE.quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:46.283445+00:00
-- url     : https://prove2.me/submissions/10295732-15c5-4b1c-9159-acecb3b92a97

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_ReciprocityTheory_CA_exists_isRegular_cons_of_modDepthGE

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
variable [IsNoetherianRing R] [Module.Finite R M]
namespace ReciprocityTheory.CA
namespace ModDepthGE
theorem _root_.solution {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R M (n + 1)) : ModDepthGE R (QuotSMulTop x M) n := by
  obtain ⟨rs, hl, hm, hr⟩ := exists_isRegular_cons_of_modDepthGE hx reg h
  exact ⟨rs, hl, hm, ((isRegular_cons_iff M x rs).mp hr).2⟩
end ModDepthGE
end ReciprocityTheory.CA
