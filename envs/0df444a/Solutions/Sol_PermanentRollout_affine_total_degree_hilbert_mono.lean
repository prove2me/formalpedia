-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_hilbert_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/e20180f0-7ff4-4b65-bd27-2c84046fdc7c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_piece_mono

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι ℂ)) :
    Monotone (affineTotalDegreeHilbert I) := by
  intro m n hmn
  exact Submodule.finrank_mono
    (affine_total_degree_filtered_piece_mono I hmn)
end PermanentRollout
