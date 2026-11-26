-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_all_subspaces_fin_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:08.670115+00:00
-- url     : https://prove2.me/submissions/fd881aaa-c2dc-4b55-bb4e-070e8ce04e39

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_subspaces_fin_zmod

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p n : ℕ) [Fact p.Prime] :
    Nat.card (Submodule (ZMod p) (Fin n → ZMod p)) = totalQBinom p n := by
  rw [Nat.card_congr (submoduleEquivSigmaFinrank (ZMod p) (Fin n → ZMod p)),
    Nat.card_sigma]
  have hfin : Module.finrank (ZMod p) (Fin n → ZMod p) = n := by simp
  rw [hfin]
  have hsum :
      (∑ k : Fin (n + 1), Nat.card (FinrankSubspaces (ZMod p) (Fin n → ZMod p) k.val)) =
        ∑ k : Fin (n + 1), qBinom p n k.val := by
    apply Fintype.sum_congr
    intro k
    exact card_subspaces_fin_zmod p n k.val (by omega)
  simpa only [totalQBinom] using hsum
end SharpIntermediateSubgroupBounds
