-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:38.975976+00:00
-- url     : https://prove2.me/submissions/ef21d2df-e5db-40b3-9999-763f5fbf23bf

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
variable {O ϖ}
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {l m n : Type} [Fintype m] {A : Matrix l m F} {B : Matrix m n F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := fun i j => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hB k j)
end PI.DatumBlockEigen.Unit
