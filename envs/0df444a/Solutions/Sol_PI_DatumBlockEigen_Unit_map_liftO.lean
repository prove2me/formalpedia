-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.map_liftO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:42.256114+00:00
-- url     : https://prove2.me/submissions/5ad46eb3-62dd-42c8-83b0-4ba80f8bc7c2

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
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {m n : Type} (N : Matrix m n F) (h : ∀ i j, N i j ∈ O) :
    (liftO O N h).map O.subtype = N := by
  ext i j; rfl
end PI.DatumBlockEigen.Unit
