-- Prove2me | solution 1 for PI.SqPairLocal.sqPairLocal_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:38.388807+00:00
-- url     : https://prove2.me/submissions/8d1469d7-6d8b-40e4-a68b-f122b84478fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Theorems.Thm_PI_SqPairLocal_pLocalAll_of_glued
import Theorems.Thm_PI_SqPairLocal_glued_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution (hLC : LocCartanPair) (h1 : LocGlob) (h2 : IntMul) (h3 : Glue)
    (h4 : SplitPlace) (h5 : InertAsm) (h6 : ModelEx) (h7 : Dict) (h8 : LocMat) (h9 : PowLoc) :
    PLocalAll := pLocalAll_of_glued h1 h2 (glued_of h3 h4 (h5 hLC h6 h7 h8 h9))
end PI.SqPairLocal
