-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.target_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:02.194804+00:00
-- url     : https://prove2.me/submissions/d48cab84-64fc-408b-97f4-7d4b832dba65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_instConj_of
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_target_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (hm : GenModOne)
    (hd : InstDecomp) (h6 : InstProper) : PI.ScMuExists.Target := by
  have h5 : InstConj := instConj_of hm hd h4
  exact target_of h1 h2 h3 h4 h5 h6
end PI.ScMuExists.UnitaryGroupMassFormula
