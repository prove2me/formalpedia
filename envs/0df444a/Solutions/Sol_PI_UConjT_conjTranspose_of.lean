-- Prove2me | solution 1 for PI.UConjT.conjTranspose_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:53.816063+00:00
-- url     : https://prove2.me/submissions/7e05ca6e-06d7-4c39-bc8a-385630ec9153

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_ConjTransposeOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
namespace PI.UConjT
theorem _root_.solution (h1 : OnbReal) (h2 : TransferStep) (h3 : BlockStep) :
    PI.UMultOne.ConjTranspose := h3 (h2 h1)
end PI.UConjT
