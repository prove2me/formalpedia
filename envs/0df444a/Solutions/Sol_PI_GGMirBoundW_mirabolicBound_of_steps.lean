-- Prove2me | solution 1 for PI.GGMirBoundW.mirabolicBound_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:06.172883+00:00
-- url     : https://prove2.me/submissions/7449951f-4c72-4de7-a5f9-0bf9002805ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Theorems.Thm_PI_GGMirBoundW_mirabolicBound_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution (hb : BaseProp) (hst : StepOf) (h1 : UnitriangularBlockExtension) (h2 : ColFacts) (h3 : ConjCol)
    (h4 : RowExists) (h5 : CharOrth) (h6 : SepLemma) : MirabolicBound :=
  mirabolicBound_of hb (hst h1 h2 h3 h4 h5 h6)
end PI.GGMirBoundW
