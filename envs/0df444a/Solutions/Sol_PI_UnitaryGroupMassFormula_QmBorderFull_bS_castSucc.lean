-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.bS_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:41.89131+00:00
-- url     : https://prove2.me/submissions/7c9f91d6-2275-4ce4-a743-ccf9e3f0d8d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es ∘ Fin.castSucc = v := by
  funext i
  first | simp [bS] | (simp only [Function.comp_apply, bS, Fin.snoc_castSucc])
end PI.UnitaryGroupMassFormula.QmBorderFull
