-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.framePower_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:46:42.196559+00:00
-- url     : https://prove2.me/submissions/4dcce4fa-f8dd-4b9d-ace1-5ac7bd748c47

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
theorem _root_.solution (q k : ℕ) :
    framePower q (k + 1) = framePower q k * q ^ k := by
  rw [framePower, Fin.prod_univ_castSucc]
  simp [framePower]
end SharpIntermediateSubgroupBounds
