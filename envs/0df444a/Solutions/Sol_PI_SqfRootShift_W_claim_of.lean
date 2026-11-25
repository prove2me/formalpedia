-- Prove2me | solution 1 for PI.SqfRootShift.W.claim_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:03.217502+00:00
-- url     : https://prove2.me/submissions/45e36d76-0560-4709-a6d4-4eddd20e8e60

import Definitions.Def_Formalism_PeriodIntegrals_SqfRootShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
namespace PI.SqfRootShift.W
theorem _root_.solution (hC : CountP) (hA : ArithP) : PI.SqfRootShift.Claim := by
  intro g r q d e _ hq hd hq8 hd16 he hq16 hd16' hg hr hg12 c T hT
  exact (hC g r (by omega) (by omega) c T hT).trans
    (hA g r q d e Fact.out hq hd hq8 hd16 he hq16 hd16' hg hr hg12)
end PI.SqfRootShift.W
