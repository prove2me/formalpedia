-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.isClosed_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:42.414336+00:00
-- url     : https://prove2.me/submissions/79dcd1ad-3019-44b3-9116-90e4f2b90ee9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply

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
variable {n r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (x : Fin n → ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ W} := by
  have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g - 1) *ᵥ x :=
    (continuous_id.sub continuous_const).matrix_mulVec continuous_const
  exact W.closed_of_finiteDimensional.preimage hc
end PI.ScMuExists.UnitaryGroupMassFormula
