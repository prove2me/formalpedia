-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.ofWitt_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:35.496832+00:00
-- url     : https://prove2.me/submissions/cc1b364e-9289-49d3-ab03-e234e4a71a2a

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
namespace Ainf
theorem _root_.solution (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Ainf.ofWitt p f (WittVector.teichmuller p a) = Ainf.teich p (Tilt.ofPerfect p f a) :=
  WittVector.map_teichmuller p _ a
end Ainf
end Reformulated.AutPerF
