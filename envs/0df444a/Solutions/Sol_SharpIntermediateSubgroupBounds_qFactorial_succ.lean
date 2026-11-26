-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qFactorial_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:58.255891+00:00
-- url     : https://prove2.me/submissions/9ce52fe2-9ad0-4203-b40f-dd50e936b56d

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
theorem _root_.solution (q n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * (q ^ (n + 1) - 1) := by
  simp [qFactorial, Finset.prod_range_succ]
end SharpIntermediateSubgroupBounds
