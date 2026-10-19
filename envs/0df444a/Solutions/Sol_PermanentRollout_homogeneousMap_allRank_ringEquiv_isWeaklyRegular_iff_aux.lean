-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_ringEquiv_isWeaklyRegular_iff_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/66a1e786-f4d3-456a-aa0d-51c6865bf3c6

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
namespace PermanentRollout
theorem _root_.solution
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (rs : List R) :
    RingTheory.Sequence.IsWeaklyRegular R rs ↔
      RingTheory.Sequence.IsWeaklyRegular S (rs.map e) := by
  apply e.toAddEquiv.isWeaklyRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  change e (r * x) = e r * e x
  exact e.map_mul r x
end PermanentRollout
