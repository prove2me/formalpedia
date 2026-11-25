-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.len_wR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:35.863807+00:00
-- url     : https://prove2.me/submissions/3e177cca-fc34-4566-a88b-e836942a5118

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNACG
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNS
namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
theorem _root_.solution (v : List (B.Mat k r)) : (wR v).length = v.length := by
  simp [wR]
end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
