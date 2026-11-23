-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.section_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:48.332352+00:00
-- url     : https://prove2.me/submissions/872aea9f-cd94-49be-8154-51c75a64aae5

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
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (a : F) :
    «section» hθ ι j hj (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) :=
  (exists_section hθ ι j hj).choose_spec.2 a
end Reformulated.AutPerF.BdRPlus
