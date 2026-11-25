-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.map_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:46.79653+00:00
-- url     : https://prove2.me/submissions/1ffa23bc-334e-4053-a5b4-108f81c1beb3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow

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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
variable {p}
open Reformulated.AutPerF.Acris
namespace Reformulated.AutPerF.Acris
theorem _root_.solution (f : R →+* S) (u : Ainf p R) (hu : Ainf.theta p R u = 1)
    (hv : Ainf.theta p S (Ainf.map p f u) = 1) : map p f (log u hu) = log (Ainf.map p f u) hv :=
  extend_log _ _ _ _ _ (AcrisZero.map_algebraMap f u)
end Reformulated.AutPerF.Acris
