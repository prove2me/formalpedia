-- Prove2me | solution 1 for PermanentRollout.sourceBlockMinor_sourceRowBlockEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/26a7c8cb-1258-45dc-8fad-f677ccb19ebe

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R]
    (b t s : ℕ) (h : Fin b)
    (X : Matrix (Fin (b * t)) (Fin s) R)
    (rows : Finset (Fin t)) (columns : Finset (Fin s)) :
    sourceBlockMinor (b * t) s X
        (rows.map (sourceRowBlockEmbedding b t h)) columns =
      sourceBlockMinor t s
        (fun row column => X (sourceRowBlockEmbedding b t h row) column)
        rows columns := by
  classical
  let rowEquiv : rows ≃ rows.map (sourceRowBlockEmbedding b t h) :=
    Finset.equivMap_tenProofs (sourceRowBlockEmbedding b t h) rows
  let matchingEquiv :
      (rows.map (sourceRowBlockEmbedding b t h) ≃ columns) ≃
        (rows ≃ columns) :=
    { toFun := fun matching => rowEquiv.trans matching
      invFun := fun matching => rowEquiv.symm.trans matching
      left_inv := by
        intro matching
        ext row
        simp
      right_inv := by
        intro matching
        ext row
        simp }
  unfold sourceBlockMinor
  refine Fintype.sum_equiv matchingEquiv _ _ ?_
  intro matching
  symm
  refine Fintype.prod_equiv rowEquiv _ _ ?_
  intro row
  simp [matchingEquiv, rowEquiv, Finset.equivMap_tenProofs]
end PermanentRollout
