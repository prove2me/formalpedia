-- Prove2me | solution 1 for PermanentRollout.sourceTreeBlockMatrix_permanent_eq_separated_minorSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/a44e4aae-2fee-4932-bdf6-3bfdd31f2fa0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceTreeBlockMatrix_permanent_eq_separated
import Theorems.Thm_PermanentRollout_sourceRowBlockMinorSum_eq_rename_minorSum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    rectangularPermanent
        (sourceBlockMatrix (b * t) s d
          (fun row column =>
            (MvPolynomial.X (row, column) :
              MvPolynomial (Fin (b * t) × Fin s) ℂ))
          (fun row column =>
            algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
              (sourceTreeMatrix b t d hd ζ tree hnodup hleaves row column))) =
      (((s - d).factorial : ℕ) :
          MvPolynomial (Fin (b * t) × Fin s) ℂ) *
        algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
          (((t - d).factorial : ℕ) : ℂ) *
        algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
          ((((t.factorial : ℕ) : ℂ) ^ (b - 1))) *
        ∑ h : Fin b,
          algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
              (subtreeCoefficient
                (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h) *
            MvPolynomial.rename
              (sourceRowBlockVariableEmbedding b t s h)
              (minorSum t s d) := by
  simpa only [sourceRowBlockMinorSum_eq_rename_minorSum] using
    (sourceTreeBlockMatrix_permanent_eq_separated
      (R := MvPolynomial (Fin (b * t) × Fin s) ℂ)
      b t s d hdpos hd hζ tree hnodup hleaves
      (fun row column =>
        (MvPolynomial.X (row, column) :
          MvPolynomial (Fin (b * t) × Fin s) ℂ)))
end PermanentRollout
