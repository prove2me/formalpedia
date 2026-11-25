-- Prove2me | solution 1 for P2M_PI_DatumBlockEigen_Main_toRows__mul__b0adba7dcda3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:43.026373+00:00
-- url     : https://prove2.me/submissions/044e0f68-f529-48da-a473-964454c040c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero

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
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
namespace PI.DatumBlockEigen.Main
theorem _root_.solution (N : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F)
    (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) :
    toRows₂ (N * x) = N.toBlocks₂₁ * toRows₁ x + N.toBlocks₂₂ * toRows₂ x := by
  ext i j
  simp [Matrix.toRows₁, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.toRows₂, Matrix.mul_apply,
    Fintype.sum_sum_type]
end PI.DatumBlockEigen.Main
