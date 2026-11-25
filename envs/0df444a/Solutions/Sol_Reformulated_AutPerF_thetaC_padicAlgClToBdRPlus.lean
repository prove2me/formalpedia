-- Prove2me | solution 1 for Reformulated.AutPerF.thetaC_padicAlgClToBdRPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:55:22.650044+00:00
-- url     : https://prove2.me/submissions/660cd5c8-c0db-4957-9b10-50366731c95a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]
namespace Reformulated.AutPerF
theorem _root_.solution (x : PadicAlgCl p) :
    BdRPlus.thetaC p (PadicComplexInt p) (padicAlgClToBdRPlus p x) = (x : ℂ_[p]) :=
  BdRPlus.thetaC_padicSection _ x
end Reformulated.AutPerF
