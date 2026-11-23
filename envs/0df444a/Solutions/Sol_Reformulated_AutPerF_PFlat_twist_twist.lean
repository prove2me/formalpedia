-- Prove2me | solution 1 for Reformulated.AutPerF.PFlat.twist_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:55.480288+00:00
-- url     : https://prove2.me/submissions/d4222e58-a024-45f2-a625-f60b486cab24

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
namespace Reformulated.AutPerF.PFlat
theorem _root_.solution (η η' : tateModule p R) (ϖ : PFlat p R) :
    (ϖ.twist η').twist η = ϖ.twist (η * η') := ext (mul_assoc _ _ _).symm
end Reformulated.AutPerF.PFlat
