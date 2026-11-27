-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.eq_ofPerfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:27.492131+00:00
-- url     : https://prove2.me/submissions/798cb4f5-96da-4d96-9233-8e27279d24e8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Bst_hom_ext


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
theorem _root_.solution (f : k →+* R ⧸ span {(p : R)}) (g : k →+* Tilt p R)
    (h : ∀ a, PreTilt.coeff 0 (g a) = f a) : g = Tilt.ofPerfect p f :=
  Perfection.hom_ext p (S := ModP R p) h
end Tilt
end Reformulated.AutPerF
