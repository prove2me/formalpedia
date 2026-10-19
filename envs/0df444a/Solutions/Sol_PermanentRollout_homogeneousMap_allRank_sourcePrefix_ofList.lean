-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_sourcePrefix_ofList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/92a7e011-fcfe-4e8b-9a4b-2a5f4fd546c9

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (j : ℕ) :
    Ideal.ofList ((List.ofFn F).take j) =
      Ideal.span (F ''
        (homogeneousMapAllKSourcePrefix k j : Set (Fin k))) := by
  classical
  change Ideal.span {p | p ∈ (List.ofFn F).take j} = _
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, heq⟩ := List.mem_take_iff_getElem.mp hp
    have hik : i < k := by
      simpa only [List.length_ofFn] using (lt_of_lt_of_le hi (Nat.min_le_right _ _))
    refine ⟨⟨i, hik⟩, ?_, ?_⟩
    · have hij : i < j := lt_of_lt_of_le hi (Nat.min_le_left _ _)
      simpa [homogeneousMapAllKSourcePrefix] using hij
    · simpa only [List.getElem_ofFn] using heq
  · rintro ⟨i, hi, rfl⟩
    have hij : i.val < j := by
      simpa [homogeneousMapAllKSourcePrefix] using hi
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val, ?_, ?_⟩
    · simpa only [List.length_ofFn] using (lt_min hij i.isLt)
    · simp
end PermanentRollout
