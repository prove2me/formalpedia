-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.associatedPrimes_eq_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:43.073843+00:00
-- url     : https://prove2.me/submissions/77524f6f-7881-4390-b569-d1e3e1cd7ea5

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_associatedPrimes_eq_minimalPrimes
import Theorems.Thm_ReciprocityTheory_CA_isCM_iff_isCMMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]
private theorem annihilator_self_eq_bot' : Module.annihilator R R = ⊥ := by
  ext r
  simp only [Module.mem_annihilator, Submodule.mem_bot]
  exact ⟨fun h => by simpa using h 1, fun h m => by simp [h]⟩
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
namespace IsCM
theorem _root_.solution (h : IsCM R) :
    associatedPrimes R R = minimalPrimes R := by
  rw [(isCM_iff_isCMMod.mp h).associatedPrimes_eq_minimalPrimes, annihilator_self_eq_bot']
end IsCM
end ReciprocityTheory.CA
