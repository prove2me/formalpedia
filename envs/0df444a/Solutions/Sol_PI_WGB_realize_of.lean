-- Prove2me | solution 1 for PI.WGB.realize_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:58.636455+00:00
-- url     : https://prove2.me/submissions/7488a17f-0e8d-4e59-8ca6-132f1c70d45a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_NatWAntiC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionC
import Theorems.Thm_PI_WGB_realize_C


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) : Realize := by
  intro n N hN lam mu f hf hfix hne
  subst hN
  exact realize_C h he ha n lam mu f hf hfix hne
end PI.WGB
