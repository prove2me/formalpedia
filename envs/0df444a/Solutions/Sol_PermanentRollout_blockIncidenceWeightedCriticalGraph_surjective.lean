-- Prove2me | solution 1 for PermanentRollout.blockIncidenceWeightedCriticalGraph_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/fd78022d-1383-4365-8987-ac4c74a0b83e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockMinorGraphPullback_rename_matrix

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (weight : Fin b → ℂ)
    (hw : ∀ h, weight h ≠ 0) (hd : 0 < d) :
    Function.Surjective
      (blockIncidenceWeightedCriticalGraph
        b t s d weight hw hd) := by
  classical
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := separatedBlockGradientIdeal b t s d weight) y
  refine ⟨Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
    (MvPolynomial.rename
      (blockMinorMatrixCoordinateLift b t s) f), ?_⟩
  change Ideal.Quotient.mk
    (separatedBlockGradientIdeal b t s d weight)
    (blockMinorGraphPullback b t s
      (MvPolynomial.rename
        (blockMinorMatrixCoordinateLift b t s) f)) = _
  rw [blockMinorGraphPullback_rename_matrix]
end PermanentRollout
