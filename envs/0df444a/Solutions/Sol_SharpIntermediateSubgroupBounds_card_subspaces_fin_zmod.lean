-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_subspaces_fin_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:21.178505+00:00
-- url     : https://prove2.me/submissions/e91036e2-455c-45ef-9d04-51b0a6131c0b

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_finrankSubspaces_eq_qBinom

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p n k : ℕ) [Fact p.Prime] (hk : k ≤ n) :
    Nat.card {W : Submodule (ZMod p) (Fin n → ZMod p) //
      Module.finrank (ZMod p) W = k} = qBinom p n k := by
  simpa using
    (card_finrankSubspaces_eq_qBinom
      (K := ZMod p) (V := Fin n → ZMod p) (k := k) (by simpa using hk))
end SharpIntermediateSubgroupBounds
