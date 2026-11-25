-- Prove2me | solution 1 for PI.ScRefExists.Sk.target_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:02.849828+00:00
-- url     : https://prove2.me/submissions/14abc00e-4c73-49ea-ac85-3e50ed17a62f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Sk
namespace PI.ScRefExists.Sk
theorem _root_.solution (h0 : Glue) (h1 : ThetaEx) (h2 : IdemLift) (h3 : LocGlob) (h4 : GlobW) :
    PI.ScRefExists.Target := h0 h1 h2 h3 h4
end PI.ScRefExists.Sk
