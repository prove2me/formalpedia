-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.frameProd_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:01.314714+00:00
-- url     : https://prove2.me/submissions/bd28ce08-e299-478f-a756-52f0a2502921

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    0 < frameProd q n k := by
  rw [frameProd]
  apply Finset.prod_pos
  intro i hi
  have hik : i.val < k := i.isLt
  have hin : i.val < n := lt_of_lt_of_le hik hk
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by omega) hin)
end SharpIntermediateSubgroupBounds
