-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/96776dea-d3c9-461b-a037-4ac0c342eb75

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_ringEquiv_isWeaklyRegular_iff_aux

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
    (e : R ≃+* S) {n : ℕ} (f : Fin n → R)
    (hregular : RingTheory.Sequence.IsWeaklyRegular S
      (List.ofFn fun i => e (f i))) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  apply (homogeneousMap_allRank_ringEquiv_isWeaklyRegular_iff_aux e
    (List.ofFn f)).mpr
  simpa only [List.map_ofFn, Function.comp_def] using hregular
end PermanentRollout
