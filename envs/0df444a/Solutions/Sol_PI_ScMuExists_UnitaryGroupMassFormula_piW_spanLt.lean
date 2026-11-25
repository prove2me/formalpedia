-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.piW_spanLt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:44.03407+00:00
-- url     : https://prove2.me/submissions/6a2e35d2-787b-4db6-bfa3-bc7a0b9ad5f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_piW_e

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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε}
variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (hF : RFrame ε e f z) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) :
    piW ε e f z x = 0 := by
  have hle : spanLt e a ≤ LinearMap.ker (piW ε e f z) := by
    rw [spanLt, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact LinearMap.mem_ker.mpr (piW_e hF b)
  exact LinearMap.mem_ker.mp (hle hx)
end PI.ScMuExists.UnitaryGroupMassFormula
