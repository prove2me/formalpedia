-- Prove2me | solution 1 for Reformulated.AutPerF.BcrisPlus.liftFracWitt_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:01.142626+00:00
-- url     : https://prove2.me/submissions/e32a9c0f-13d1-4132-9934-baf351551a1d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
namespace BcrisPlus
theorem _root_.solution (g : WittVector p k →+* R) (a : WittVector p k) :
    BcrisPlus.liftFracWitt p g (algebraMap _ _ a) =
      algebraMap (Acris p R) _ (algebraMap (Ainf p R) _ (Ainf.liftWitt p g a)) :=
  fracWittLift_algebraMap p _ _ a
end BcrisPlus
end Reformulated.AutPerF
