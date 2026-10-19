-- Prove2me | solution 1 for PermanentRollout.isSMulRegular_iff_avoid_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/92ba1209-1ca5-481a-b097-83dd5330b985

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔
      ∀ P ∈ associatedPrimes R M, r ∉ P := by
  have heq := biUnion_associatedPrimes_eq_compl_regular R M
  constructor
  · intro hregular P hP hrP
    have hunion : r ∈ ⋃ Q ∈ associatedPrimes R M, Q :=
      Set.mem_iUnion₂_of_mem hP hrP
    have hnot : r ∈ {x : R | IsSMulRegular M x}ᶜ :=
      heq ▸ hunion
    exact hnot hregular
  · intro havoid
    by_contra hnot
    have hcompl : r ∈ {x : R | IsSMulRegular M x}ᶜ := hnot
    have hunion : r ∈ ⋃ Q ∈ associatedPrimes R M, Q :=
      heq.symm ▸ hcompl
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hunion
    obtain ⟨hassoc, hrP⟩ := Set.mem_iUnion.mp hP
    exact havoid P hassoc hrP
end PermanentRollout
