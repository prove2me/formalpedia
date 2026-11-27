-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeToProjective_proof_7e3d144d8afd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:12.277044+00:00
-- url     : https://prove2.me/submissions/eb927710-b8d3-4453-b2fe-32ad74948f0e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaneSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeToProjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneIntegral_space_one_1f6611ae8ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_bot_space_7322bb62afb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_not_mem_bot_952292a2748a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_space_dim_45905c840704


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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeToProjective
theorem _root_.solution (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConePolar.Statement)
    (h₃ : PlaneSliceMass.Statement) : ConeToProjective.Statement := by
  intro n e h J F ℓ g hJ hF hℓ hg hgc
  obtain ⟨κ, hκ⟩ := h₂ e
  have hplane := hκ (e + 1) (HermNorm.std (e + 1)) ⊥ (Pi.single 0 1) (fun _ => 1)
    (isProjPrime_bot_space e) (space_dim (e + 1)) (linForm_single_not_mem_bot 0)
    (fun _ _ _ => rfl) continuousOn_const
  rw [coneIntegral_space_one, linForm_single, bot_sup_eq, h₃ e, mul_one] at hplane
  rw [hκ n h J ℓ g hJ (h₁ ℂ n (e + 1) J F hJ hF) hℓ hg hgc, ← hplane, one_mul]
end ConeToProjective
end GroundTheory.Heights₂.Heights
