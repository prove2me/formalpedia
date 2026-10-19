-- Prove2me | solution 1 for PermanentRollout.sourceBlockAlpha_eq_permanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/bf402e6f-3e5f-421c-b959-165794ae6801

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r d : ℕ}
    (U : Matrix (Fin r) (Fin (r - d)) ℂ)
    (omitted : Finset (Fin r))
    (rowEquiv : Fin (r - d) ≃ {row : Fin r // row ∉ omitted}) :
    sourceBlockAlpha r d U omitted =
      Matrix.permanent
        (fun i j => U (rowEquiv i).val j) := by
  classical
  let matchingEquiv :
      ({row : Fin r // row ∉ omitted} ≃ Fin (r - d)) ≃
        Equiv.Perm (Fin (r - d)) :=
    { toFun := fun matching => matching.symm.trans rowEquiv.symm
      invFun := fun matching => rowEquiv.symm.trans matching.symm
      left_inv := by
        intro matching
        ext row
        simp
      right_inv := by
        intro matching
        ext column
        simp }
  unfold sourceBlockAlpha Matrix.permanent
  refine Fintype.sum_equiv matchingEquiv _ _ ?_
  intro matching
  refine Fintype.prod_equiv matching _ _ ?_
  intro row
  simp [matchingEquiv]
end PermanentRollout
