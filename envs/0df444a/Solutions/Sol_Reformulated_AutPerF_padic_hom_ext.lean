-- Prove2me | solution 1 for Reformulated.AutPerF.padic_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:53.472719+00:00
-- url     : https://prove2.me/submissions/d1dbace6-0acd-47b0-86f7-7c6f9e7af06a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap

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
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]
variable {R S U}
variable {p}
namespace Reformulated.AutPerF
theorem _root_.solution {B : Type*} [CommRing B] {f g : ℚ_[p] →+* B}
    (h : ∀ a : ℤ_[p], f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext h)
end Reformulated.AutPerF
