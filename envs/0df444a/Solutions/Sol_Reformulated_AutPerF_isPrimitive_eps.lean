-- Prove2me | solution 1 for Reformulated.AutPerF.isPrimitive_eps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:10.304394+00:00
-- url     : https://prove2.me/submissions/deb85114-77be-444b-bf06-31224378525e

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
variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]
variable [CharZero R]
variable (p R)
namespace Reformulated.AutPerF
theorem _root_.solution : IsPrimitive (eps p R) := (exists_isPrimitive p R).choose_spec
end Reformulated.AutPerF
