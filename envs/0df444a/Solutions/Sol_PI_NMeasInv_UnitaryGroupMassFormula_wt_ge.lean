-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.wt_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:35.043092+00:00
-- url     : https://prove2.me/submissions/4652543a-2d5a-41ff-a5be-0e9d19cb5088

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_MeasureContractionFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory NumberField
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (lam : ℝ) (hlam : 1 ≤ lam) (b : Fin r) : lam ≤ wt r lam b := by
  unfold wt
  have := b.isLt
  calc lam = lam ^ 1 := (pow_one _).symm
    _ ≤ lam ^ (r - b.val) := pow_le_pow_right₀ hlam (by omega)
end PI.NMeasInv.UnitaryGroupMassFormula
