-- Prove2me | solution 1 for Reformulated.AutPerF.fracWittLift_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:36.352678+00:00
-- url     : https://prove2.me/submissions/f53e1efd-dfd1-4fe9-826e-2619f64ea49f

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
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
namespace Reformulated.AutPerF
theorem _root_.solution {B : Type*} [CommRing B] (f : WittVector p k →+* B)
    (h : IsUnit (p : B)) (a : WittVector p k) : fracWittLift p f h (algebraMap _ _ a) = f a :=
  IsLocalization.lift_eq _ a
end Reformulated.AutPerF
