-- Prove2me | solution 1 for ReciprocityTheory.CA.socle_of_max_mem_ass
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:19.288384+00:00
-- url     : https://prove2.me/submissions/f9c2cb7d-63de-41df-81f4-9014e6bb4b5e

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE

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
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N]
    (h : maximalIdeal R ∈ associatedPrimes R N) :
    ∃ a : N, a ≠ 0 ∧ ∀ z ∈ maximalIdeal R, z • a = 0 := by
  obtain ⟨-, a, ha⟩ := Submodule.isAssociatedPrime_iff.mp h
  refine ⟨a, ?_, fun z hz => ?_⟩
  · rintro rfl
    apply (maximalIdeal.isMaximal R).ne_top
    rw [ha, eq_top_iff]
    intro r _
    exact Submodule.mem_colon_singleton.mpr (by simp)
  · rw [ha] at hz
    simpa using Submodule.mem_colon_singleton.mp hz
end ReciprocityTheory.CA
