-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.theta_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:54.627837+00:00
-- url     : https://prove2.me/submissions/5d1fa310-69fe-4a69-8efc-824764c199a4

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
variable [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BdRPlus
variable {p}
variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (x : L) :
    theta p R («section» hθ ι j hj x) = j x := (exists_section hθ ι j hj).choose_spec.1 x
end Reformulated.AutPerF.BdRPlus
