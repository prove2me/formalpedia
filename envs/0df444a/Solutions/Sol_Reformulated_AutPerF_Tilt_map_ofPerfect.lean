-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.map_ofPerfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:42.293193+00:00
-- url     : https://prove2.me/submissions/f240f7cf-e50a-4cfa-8348-43ed947a2179

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
theorem _root_.solution (e : R →+* S) (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Tilt.map p e (Tilt.ofPerfect p f a) =
      Tilt.ofPerfect p ((Ideal.quotientMap _ e (span_natCast_le_comap p e)).comp f) a :=
  Tilt.ext fun _ => rfl
end Tilt
end Reformulated.AutPerF
