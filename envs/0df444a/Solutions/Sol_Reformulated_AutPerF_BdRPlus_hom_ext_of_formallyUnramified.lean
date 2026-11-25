-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.hom_ext_of_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:25.57655+00:00
-- url     : https://prove2.me/submissions/214a19e0-97b0-483b-a4ed-41f033884e14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_iInf_ker_theta_pow
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap

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
theorem _root_.solution [Algebra.FormallyUnramified F L] {s₁ s₂ : L →+* BdRPlus p R}
    (hF : ∀ a : F, s₁ (algebraMap F L a) = s₂ (algebraMap F L a))
    (hθ : ∀ x, theta p R (s₁ x) = theta p R (s₂ x)) : s₁ = s₂ := by
  letI : Algebra F (BdRPlus p R) := (s₁.comp (algebraMap F L)).toAlgebra
  have := Algebra.FormallyUnramified.ext_of_iInf (R := F) (I := RingHom.ker (theta p R))
    iInf_ker_theta_pow (g₁ := { s₁ with commutes' := fun _ => rfl })
    (g₂ := { s₂ with commutes' := fun a => (hF a).symm }) (fun x => by
      rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hθ x)
  exact RingHom.ext fun x => AlgHom.congr_fun this x
end Reformulated.AutPerF.BdRPlus
