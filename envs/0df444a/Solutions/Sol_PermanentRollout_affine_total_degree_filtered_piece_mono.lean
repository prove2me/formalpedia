-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_piece_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/c258ee09-b126-4005-9f33-1d82c3f2ec9a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    {m n : ℕ} (h : m ≤ n) :
    affineTotalDegreeFilteredPiece I m ≤
      affineTotalDegreeFilteredPiece I n := by
  apply Submodule.map_mono
  intro p hp
  apply (MvPolynomial.mem_restrictTotalDegree _ _ p).mpr
  exact ((MvPolynomial.mem_restrictTotalDegree _ _ p).mp hp).trans h
end PermanentRollout
