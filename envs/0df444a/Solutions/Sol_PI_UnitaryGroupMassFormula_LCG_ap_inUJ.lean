-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:42.099103+00:00
-- url     : https://prove2.me/submissions/c35885c5-f7a7-45db-a9fd-aa84a4f36de9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := by
  first
    | exact g.2
    | (have h := g.2
       simpa [Formalism.REAL.UJ, Formalism.REAL.inUJ] using h)
end PI.UnitaryGroupMassFormula.LCG
