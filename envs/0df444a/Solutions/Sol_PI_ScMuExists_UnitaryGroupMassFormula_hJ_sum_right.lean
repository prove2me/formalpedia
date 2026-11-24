-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.hJ_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:33.893461+00:00
-- url     : https://prove2.me/submissions/50cf88db-4a6d-4f79-8eb1-50882aabcbdd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart

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
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {ι : Type*} (s : Finset ι) (u : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε u (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε u (g i) := by
  exact map_sum (hJL ε u) g s
end PI.ScMuExists.UnitaryGroupMassFormula
