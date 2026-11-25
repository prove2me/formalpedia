-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_homR_215a0de6330c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:12.459862+00:00
-- url     : https://prove2.me/submissions/26357af7-d083-43b3-8cb8-f1c3bf9d8510

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree

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
    (chartPsi e R Q j S).comp (chartHomR e R Q j S) =
      (algebraMap _ (ChartBj e R Q j)).comp (algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R))) := by
  refine IsLocalization.ringHom_ext S (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, chartHomR_algebraMap, chartPsi, IsLocalization.lift_eq]
  exact RingHom.congr_fun (chartPsi0_comp e R Q j) a
end GroundTheory.Heights₂.Heights.Vertical
