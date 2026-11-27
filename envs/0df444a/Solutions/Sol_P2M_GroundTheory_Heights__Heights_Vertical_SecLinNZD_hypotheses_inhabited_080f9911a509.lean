-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecLinNZD_hypotheses_inhabited_080f9911a509
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:12:50.787472+00:00
-- url     : https://prove2.me/submissions/a43d0c98-792b-466f-868b-88123f7f44fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_pointPar_algebraicIndependent_557120b59e17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c


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
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SecLinNZD
theorem _root_.solution :
    AlgebraicIndependent ℚ pointPar ∧ IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨pointPar_algebraicIndependent, isProjPrime_point ℚ, isChowForm_point ℚ, linForm_one_not_mem_point ℚ⟩
end SecLinNZD
end GroundTheory.Heights₂.Heights.Vertical
