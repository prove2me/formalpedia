-- Prove2me | solution 1 for Reformulated.AutPerF.fracWitt_frobenius_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:41.983865+00:00
-- url     : https://prove2.me/submissions/2486ef9e-efd8-4c08-bdc4-9b8a12615737

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients

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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
theorem _root_.solution (a : WittVector p k) :
    WittVector.FractionRing.frobenius p k (algebraMap _ _ a) =
      algebraMap _ _ (WittVector.frobenius a) := by
  rw [WittVector.FractionRing.frobenius, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl
end Reformulated.AutPerF
