-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualCanonicalCleanedHistorySymm_eq_direct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/d00193c7-f3db-428a-8751-09e45aa11b89

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {L : ℕ} (j : Fin L) (β : Type*)
    (selected : β) (before : Fin j.val → β)
    (later : Fin (L - j.val) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β).symm (selected, (before, later)) =
      directDSVSelectedCopyLocalHistoryEquiv
        j (selected, (before, later)) := by
  apply (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    j β).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact
      (directDSVSelectedCopyLocalHistoryEquiv_hit
        j selected before later).symm
  · apply Prod.ext
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_before
          j selected before later i).symm
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_after
          j selected before later i).symm
end QuantumParallelRepetition
