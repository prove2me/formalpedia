-- Prove2me | solution 1 for ZetaZeros.D.EllReg.stepOfParts_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:59.127686+00:00
-- url     : https://prove2.me/submissions/1ae337cc-5d66-450a-9f87-0db9dbee8aab

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace ZetaZeros.D.EllReg
theorem _root_.solution (hD : DecomposeOf) (hF : FiniteWeighted) (hE : EpsLimit) (hS : StepCore) :
    StepOfParts :=
  fun hSL hW hCB hK hPF hDE hFP hPL hWF _ hC => hS hSL hW hCB hK (hD hPF hDE hFP hPL hWF) hF hE hC
end ZetaZeros.D.EllReg
