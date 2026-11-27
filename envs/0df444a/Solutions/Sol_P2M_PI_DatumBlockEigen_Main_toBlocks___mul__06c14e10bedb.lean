-- Prove2me | solution 1 for P2M_PI_DatumBlockEigen_Main_toBlocks___mul__06c14e10bedb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:45.314334+00:00
-- url     : https://prove2.me/submissions/778985e8-f4f0-429f-9b71-d10e1827606f

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
    (N * P).toBlocks₁₁ = N.toBlocks₁₁ * P.toBlocks₁₁ + N.toBlocks₁₂ * P.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.mul_apply,
    Fintype.sum_sum_type]
end PI.DatumBlockEigen.Main
