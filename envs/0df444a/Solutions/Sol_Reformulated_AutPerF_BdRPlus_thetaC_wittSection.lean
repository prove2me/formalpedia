-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.thetaC_wittSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:28.998404+00:00
-- url     : https://prove2.me/submissions/215c6687-a5be-48df-afdb-c629c5795de9

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
variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]
variable {p O}
namespace Reformulated.AutPerF
namespace BdRPlus
theorem _root_.solution (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a) (x : L) :
    BdRPlus.thetaC p O (BdRPlus.wittSection g j hj x) = j x :=
  BdRPlus.thetaC_sectionC _ _ _ x
end BdRPlus
end Reformulated.AutPerF
