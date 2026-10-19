-- Prove2me | solution 1 for PermanentRollout.sourceRowBlockMinorSum_eq_rename_minorSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/30fd1183-5643-43b6-a0da-ed62bd2207de

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceRowBlockMinorSum_eq_local_minors

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (h : Fin b) :
    sourceRowBlockMinorSum b t s d
        (fun row column =>
          (MvPolynomial.X (row, column) :
            MvPolynomial (Fin (b * t) × Fin s) ℂ)) h =
      MvPolynomial.rename
        (sourceRowBlockVariableEmbedding b t s h)
        (minorSum t s d) := by
  classical
  rw [sourceRowBlockMinorSum_eq_local_minors b t s d h
    (fun row column =>
      (MvPolynomial.X (row, column) :
        MvPolynomial (Fin (b * t) × Fin s) ℂ))]
  unfold minorSum sourceBlockMinor
  simp only [map_sum, map_prod, MvPolynomial.rename_X]
  rfl
end PermanentRollout
