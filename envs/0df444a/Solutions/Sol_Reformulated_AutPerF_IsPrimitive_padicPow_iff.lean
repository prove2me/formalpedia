-- Prove2me | solution 1 for Reformulated.AutPerF.IsPrimitive.padicPow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:38.024704+00:00
-- url     : https://prove2.me/submissions/e5f8bd9e-a688-48d2-befa-cf5ee715cae1

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
namespace Reformulated.AutPerF
namespace IsPrimitive
theorem _root_.solution {ε : tateModule p R} (hε : IsPrimitive ε) (a : ℤ_[p]) :
    IsPrimitive (padicPow ε a) ↔ IsUnit a := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [isPrimitive_iff, seq_padicPow, Ne, (hε.isPrimitiveRoot 1).pow_eq_one_iff_dvd,
    ← ZMod.natCast_eq_zero_iff, cast_val_toZModPow, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]
end IsPrimitive
end Reformulated.AutPerF
