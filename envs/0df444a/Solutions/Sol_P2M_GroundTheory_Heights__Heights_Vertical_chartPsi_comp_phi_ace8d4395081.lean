-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_phi_ace8d4395081
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:10.843974+00:00
-- url     : https://prove2.me/submissions/ed9b7cb3-2b4b-4e83-af37-9029b453e36f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_homR_215a0de6330c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {D : Type*} [CommRing D] {n : ℕ}
variable (e : ℕ) (R : Type*) [CommRing R] [Algebra (MvPolynomial (Par e n) D) R]
variable (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D))
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution [IsLocalization S R] :
    (chartPsi e R Q j S).comp (chartPhi e R Q j S) = algebraMap _ (ChartBj e R Q j) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_))
  · have h := RingHom.congr_fun (chartPsi_comp_homR e R Q j S) r
    simp only [RingHom.comp_apply, chartPhi, Ideal.Quotient.lift_mk, chartPhi0, eval₂Hom_C] at h ⊢
    exact h
  · simp only [RingHom.comp_apply, chartPhi, Ideal.Quotient.lift_mk, chartPhi0, eval₂Hom_X', chartPsi,
      IsLocalization.lift_eq, chartPsi0_coord]
    rfl
end GroundTheory.Heights₂.Heights.Vertical
