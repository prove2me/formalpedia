-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_kappa_aa187d03048f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:44.954089+00:00
-- url     : https://prove2.me/submissions/f7995f8a-da68-4ab8-8b30-f32255c67a28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjSecDomain
variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
variable {W A}
variable (W A)
variable {W A}
variable (W A)
variable {W A}
namespace GroundTheory.Heights₂.Heights.ProjSecDomain
theorem _root_.solution : (chi W A).comp (kappa W A) = algebraMap (Kf e) (S W A) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) ?_
  rw [RingHom.comp_assoc, kappa, IsLocalization.lift_comp, ← RingHom.comp_assoc, chi,
    IsLocalization.lift_comp, psi_comp_projHom]
end GroundTheory.Heights₂.Heights.ProjSecDomain
