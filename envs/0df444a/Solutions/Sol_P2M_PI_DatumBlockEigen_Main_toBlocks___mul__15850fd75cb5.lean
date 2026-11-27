-- Prove2me | solution 1 for P2M_PI_DatumBlockEigen_Main_toBlocks___mul__15850fd75cb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:49.869212+00:00
-- url     : https://prove2.me/submissions/86fdbad9-2f9f-4cc4-9c4b-aeea21b88c10

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
theorem _root_.solution (N P : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) :
    (N * P).toBlocks₂₁ = N.toBlocks₂₁ * P.toBlocks₁₁ + N.toBlocks₂₂ * P.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply,
    Fintype.sum_sum_type]
end PI.DatumBlockEigen.Main
