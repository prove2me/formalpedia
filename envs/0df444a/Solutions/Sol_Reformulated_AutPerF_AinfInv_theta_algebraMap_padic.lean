-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.theta_algebraMap_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:07.910161+00:00
-- url     : https://prove2.me/submissions/608f5304-866f-4638-877e-ed5107f9c79c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_algebraMap_padicInt
import Theorems.Thm_Reformulated_AutPerF_padic_hom_ext


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
variable {p}
namespace Reformulated.AutPerF
namespace AinfInv
theorem _root_.solution (g : ℤ_[p] →+* R) (j : ℚ_[p] →+* Localization.Away (p : R))
    (hj : ∀ a : ℤ_[p], j (algebraMap _ _ a) = algebraMap R _ (g a)) (x : ℚ_[p]) :
    AinfInv.theta p R (algebraMap ℚ_[p] _ x) = j x :=
  RingHom.congr_fun (padic_hom_ext (f := (AinfInv.theta p R).comp (algebraMap ℚ_[p] _)) (g := j)
    (fun a => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (AinfInv p R), AinfInv.theta_algebraMap,
        Ainf.theta_algebraMap_padicInt g, hj])) x
end AinfInv
end Reformulated.AutPerF
