-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.frob_liftWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:05.012258+00:00
-- url     : https://prove2.me/submissions/72e6c6f3-02be-44b6-b045-d0d2ef3c2974

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_frob_ofWitt

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
namespace Ainf
theorem _root_.solution (g : WittVector p k →+* R) (x : WittVector p k) :
    Ainf.frob p R (Ainf.liftWitt p g x) = Ainf.liftWitt p g (WittVector.frobenius x) :=
  Ainf.frob_ofWitt _ x
end Ainf
end Reformulated.AutPerF
