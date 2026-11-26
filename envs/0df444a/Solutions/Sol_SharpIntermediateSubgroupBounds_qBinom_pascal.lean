-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qBinom_pascal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:47.457917+00:00
-- url     : https://prove2.me/submissions/9fa1f747-6d17-4603-bc19-1443f3204720

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
theorem _root_.solution (q : ℕ) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    qBinom q n k = qBinom q (n - 1) (k - 1) + q ^ k * qBinom q (n - 1) k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simpa using qBinom_succ_succ q n k
end SharpIntermediateSubgroupBounds
