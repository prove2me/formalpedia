-- Prove2me | solution 1 for PermanentRollout.exists_high_homogeneousSubmodule_le_homogeneousMapIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/ec542f6f-2d4d-48cb-829e-a52f867cf45f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ p : MvPolynomial ι ℂ,
        p.IsHomogeneous n → p ∈ homogeneousMapIdeal F := by
  obtain ⟨N, hN⟩ :=
    exists_idealOfVars_pow_le_homogeneousMapIdeal F hzero
  refine ⟨N, ?_⟩
  intro n hn p hp
  exact hN (homogeneous_mem_idealOfVars_pow_of_le hp hn)
end PermanentRollout
