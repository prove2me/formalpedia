-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.eq_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:00.612872+00:00
-- url     : https://prove2.me/submissions/781f1018-dc64-4964-931d-fcd78e29b01e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_hom_ext_of_formallyUnramified
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_section
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_section_algebraMap

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
theorem _root_.solution [Algebra.FormallyEtale F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (s : L →+* BdRPlus p R)
    (h₁ : ∀ x, theta p R (s x) = j x)
    (h₂ : ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a)) :
    s = «section» hθ ι j hj :=
  hom_ext_of_formallyUnramified (F := F) (fun a => by rw [h₂, section_algebraMap])
    (fun x => by rw [h₁, theta_section])
end Reformulated.AutPerF.BdRPlus
