-- Prove2me | solution 1 for Reformulated.AutPerF.PFlat.twist_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:00.489533+00:00
-- url     : https://prove2.me/submissions/60e7aa59-73e3-4c28-b55a-e267406b0ad0

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter

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
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Tilt tateModule
open Reformulated.AutPerF.PFlat
variable [IsDomain R] [CharZero R]
variable [ValuationRing R]
namespace Reformulated.AutPerF.PFlat
theorem _root_.solution (ϖ' ϖ : PFlat p R) : ϖ.twist (ϖ'.div ϖ) = ϖ' :=
  (twist_surjective ϖ ϖ').choose_spec
end Reformulated.AutPerF.PFlat
