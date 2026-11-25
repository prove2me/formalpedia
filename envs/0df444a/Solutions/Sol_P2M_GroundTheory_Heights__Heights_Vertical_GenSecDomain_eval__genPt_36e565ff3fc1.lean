-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__genPt_36e565ff3fc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:58.435274+00:00
-- url     : https://prove2.me/submissions/af1d8b51-33ed-4d1c-a862-1a39883714cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] (e : ℕ)
omit [Q.IsPrime]
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (p : MvPolynomial (Fin n) k) :
    eval₂ (algebraMap k (Fn Q)) (genPt Q) p = algebraMap _ (Fn Q) (Ideal.Quotient.mk Q p) := by
  have h : (eval₂Hom (algebraMap k (Fn Q)) (genPt Q)) =
      (algebraMap (MvPolynomial (Fin n) k ⧸ Q) (Fn Q)).comp (Ideal.Quotient.mk Q) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · simp only [coe_eval₂Hom, eval₂_C, RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k ⧸ Q) (Fn Q)]
      rfl
    · simp [genPt]
  exact congrArg (fun f : MvPolynomial (Fin n) k →+* Fn Q => f p) h
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
