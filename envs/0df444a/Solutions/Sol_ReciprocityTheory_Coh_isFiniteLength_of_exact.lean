-- Prove2me | solution 1 for ReciprocityTheory.Coh.isFiniteLength_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:18.167191+00:00
-- url     : https://prove2.me/submissions/044d8949-5f65-4920-a5ea-c59f464caf3a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
namespace ReciprocityTheory.Coh
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Exact f g)
    (hM : IsFiniteLength R M) (hP : IsFiniteLength R P) : IsFiniteLength R N := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at *
  obtain ⟨_, _⟩ := hM
  obtain ⟨_, _⟩ := hP
  have e : LinearMap.range f = LinearMap.ker g := h.linearMap_ker_eq.symm
  exact ⟨isNoetherian_of_range_eq_ker f g e, isArtinian_of_range_eq_ker f g e⟩
end ReciprocityTheory.Coh
