-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_card_residual_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/f7033438-9ed4-43e4-8546-c13f22339f97

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (rows : T ↪ B) (cols : T ↪ A)
    (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card
      ({a : A // a ∉ Set.range cols} ≃
        {b : B // b ∉ Set.range rows}) =
      (Fintype.card A - Fintype.card T).factorial := by
  classical
  have hrem :
      Fintype.card {a : A // a ∉ Set.range cols} =
        Fintype.card {b : B // b ∉ Set.range rows} := by
    rw [matching_card_compl_range, matching_card_compl_range, hcard]
  let e := Fintype.equivOfCardEq hrem
  rw [Fintype.card_equiv e, matching_card_compl_range]
end PermanentFormulaLowerBound
