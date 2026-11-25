-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.coeff_ofPerfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:38.095503+00:00
-- url     : https://prove2.me/submissions/18ac1229-55c2-4144-8484-9c9419cafb72

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section

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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
namespace Tilt
theorem _root_.solution (f : k →+* R ⧸ span {(p : R)}) (n : ℕ) (a : k) :
    PreTilt.coeff n (Tilt.ofPerfect p f a) = f ((frobeniusEquiv k p).symm^[n] a) := rfl
end Tilt
end Reformulated.AutPerF
