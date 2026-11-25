-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.isClosedEmbedding_uMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:43.117829+00:00
-- url     : https://prove2.me/submissions/60103eae-45fb-417b-9d53-7c23e3b1e148

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_Proper
import Theorems.Thm_Formalism_REAL_uJEmb


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
open scoped Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.uJEmb n ε).1
end PI.ScMuExists.UnitaryGroupMassFormula
