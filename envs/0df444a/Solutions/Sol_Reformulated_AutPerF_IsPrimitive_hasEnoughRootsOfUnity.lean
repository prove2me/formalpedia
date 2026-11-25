-- Prove2me | solution 1 for Reformulated.AutPerF.IsPrimitive.hasEnoughRootsOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:35.138682+00:00
-- url     : https://prove2.me/submissions/41bfdb34-ef0a-4182-a4cc-3e649cd96fbd

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
variable [IsDomain R]
namespace Reformulated.AutPerF
namespace IsPrimitive
theorem _root_.solution {ε : tateModule p R} (hε : IsPrimitive ε) (n : ℕ) :
    HasEnoughRootsOfUnity R (p ^ n) :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ⟨⟨_, hε.isPrimitiveRoot n⟩, rootsOfUnity.isCyclic _ _⟩
end IsPrimitive
end Reformulated.AutPerF
