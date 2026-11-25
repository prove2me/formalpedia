-- Prove2me | solution 1 for ReciprocityTheory.CA.ModDepthGE.le_ringKrullDim_quotient_of_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:23.599138+00:00
-- url     : https://prove2.me/submissions/64f09340-6310-44d4-8244-08a252dee951

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactRest_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Theorems.Thm_ReciprocityTheory_CA_length_le_of_isRegular_of_mem_associatedPrimes

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
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
namespace ReciprocityTheory.CA
namespace ModDepthGE
theorem _root_.solution {n : ℕ}
    (h : ModDepthGE R M n) {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  subst hlen
  exact length_le_of_isRegular_of_mem_associatedPrimes rs hmem hreg hp
end ModDepthGE
end ReciprocityTheory.CA
