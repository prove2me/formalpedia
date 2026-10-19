-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_piece_eventual_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/55cc99ed-446b-4a79-a92e-2f611a8ae7bf

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_piece_eventually_eq_top

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
    [Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I)] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      Module.finrank ℂ (affineTotalDegreeFilteredPiece I m) =
        Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I) := by
  obtain ⟨n, hn⟩ := affine_total_degree_filtered_piece_eventually_eq_top I
  refine ⟨n, fun m hm => ?_⟩
  rw [hn m hm, finrank_top]
end PermanentRollout
