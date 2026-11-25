-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_g_9edd29643ac0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:29.306253+00:00
-- url     : https://prove2.me/submissions/3071a0e6-351d-4836-9e0f-d6f947cd4736

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDomain_chi_kappa_aa187d03048f

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
theorem _root_.solution (s : S W A) : chi W A (g W A s) = s := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
  have : (chi W A).comp (phi W A) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, phi_C, ← RingHom.comp_apply, chi_kappa]; rfl
    · rw [RingHom.comp_apply, phi, eval₂Hom_X', chi, IsLocalization.lift_eq, psi_mk, map_X]
  show chi W A (phi W A f) = _
  exact RingHom.congr_fun this f
end GroundTheory.Heights₂.Heights.ProjSecDomain
