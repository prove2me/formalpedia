-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.frameProd_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:53.387873+00:00
-- url     : https://prove2.me/submissions/4f2f7eb5-b100-4ee7-a7cc-5eed1b7e0e09

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
theorem _root_.solution (q n k : ℕ) :
    frameProd q n (k + 1) = frameProd q n k * (q ^ n - q ^ k) := by
  rw [frameProd, Fin.prod_univ_castSucc]
  simp [frameProd]
end SharpIntermediateSubgroupBounds
