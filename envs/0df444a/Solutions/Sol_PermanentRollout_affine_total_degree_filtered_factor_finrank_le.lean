-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_factor_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/b96659cb-538d-493e-8d39-ad199b649c1d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_factor_surjective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι] {I J : Ideal (MvPolynomial ι ℂ)}
    (hIJ : I ≤ J) (n : ℕ) :
    Module.finrank ℂ (affineTotalDegreeFilteredPiece J n) ≤
      Module.finrank ℂ (affineTotalDegreeFilteredPiece I n) := by
  apply LinearMap.finrank_le_finrank_of_surjective
  exact affine_total_degree_filtered_factor_surjective hIJ n
end PermanentRollout
