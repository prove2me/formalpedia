-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qFactorial_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:59.846211+00:00
-- url     : https://prove2.me/submissions/4fff9d35-ad61-4802-afad-76ab255a7f21

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
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : 0 < qFactorial q n := by
  rw [qFactorial]
  exact Finset.prod_pos fun i hi ↦ by
    have hiq : 1 < q ^ (i + 1) := by
      exact one_lt_pow₀ (by omega) (by omega)
    omega
end SharpIntermediateSubgroupBounds
