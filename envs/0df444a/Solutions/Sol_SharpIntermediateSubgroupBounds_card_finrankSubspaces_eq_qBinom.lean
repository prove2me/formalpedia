-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_finrankSubspaces_eq_qBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:45.41662+00:00
-- url     : https://prove2.me/submissions/afb6d481-dd89-4b7f-90ec-20822250c1cb

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_mul_frameProd
import Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_finrankSubspaces_mul_frameProd

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (FinrankSubspaces K V k) =
      qBinom (Fintype.card K) (Module.finrank K V) k := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hpos : 0 < frameProd (Fintype.card K) k k := frameProd_pos hq le_rfl
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
        frameProd (Fintype.card K) (Module.finrank K V) k :=
      card_finrankSubspaces_mul_frameProd hk
    _ = qBinom (Fintype.card K) (Module.finrank K V) k *
        frameProd (Fintype.card K) k k := (qBinom_mul_frameProd hq hk).symm
end SharpIntermediateSubgroupBounds
