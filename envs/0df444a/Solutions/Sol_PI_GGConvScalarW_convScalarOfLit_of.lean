-- Prove2me | solution 1 for PI.GGConvScalarW.convScalarOfLit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:49.918825+00:00
-- url     : https://prove2.me/submissions/faeda4d4-cd28-4ad6-8d44-272d045c6014

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_ConvScalarOfLitOf
import Theorems.Thm_PI_GGConvScalarW_convScalar_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
namespace PI.GGConvScalarW
theorem _root_.solution (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff)
    (h5 : RankLeOne) (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) :
    ConvScalarOfLit := by
  exact fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm
end PI.GGConvScalarW
