-- Prove2me | solution 1 for Reformulated.AutPerF.PFlat.twist_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:19.348152+00:00
-- url     : https://prove2.me/submissions/17b97b5b-a687-4f82-bf88-951500a73a7a

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
namespace Reformulated.AutPerF.PFlat
theorem _root_.solution (ϖ : PFlat p R) : Function.Injective fun η => ϖ.twist η := by
  intro η η' h
  refine tateModule.ext_seq fun n => mul_right_cancel₀ (seq_ne_zero ϖ n) ?_
  have h1 : η.1 * ϖ.1 = η'.1 * ϖ.1 := by
    rw [← twist_val, ← twist_val]
    exact congrArg Subtype.val h
  rw [← map_mul, ← map_mul, h1]
end Reformulated.AutPerF.PFlat
