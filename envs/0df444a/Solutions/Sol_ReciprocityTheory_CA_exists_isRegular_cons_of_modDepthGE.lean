-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_isRegular_cons_of_modDepthGE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:57.6188+00:00
-- url     : https://prove2.me/submissions/48d136dd-c914-428a-bb16-f0caee575e72

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_ReciprocityTheory_CA_exists_regular_sequence_cons

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
theorem _root_.solution {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) {n : ℕ} (h : ModDepthGE R M (n + 1)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M (x :: rs) :=
  exists_regular_sequence_cons n M hx reg h
end ReciprocityTheory.CA
