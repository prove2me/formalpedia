-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SectionNef_hypotheses_inhabited_9689f7f2198a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:08.537806+00:00
-- url     : https://prove2.me/submissions/ed9694b8-3e90-4fc9-8a2c-7ad7345f4401

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isMultiHomog_X_zero_b47684ca621c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace SectionNef
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
      ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
        ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
      IsRegularSection (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) (fun _ => ((1 : ℕ) : ℤ))
        (MvPolynomial.X ⟨(), 0⟩) 1 := by
  refine ⟨isMultiProjPrime_bot, projectiveLine_dim, isRegularSection_form Ideal.isPrime_bot
    isMultiHomog_X_zero ?_⟩
  rw [Ideal.mem_bot]
  exact MvPolynomial.X_ne_zero _
end SectionNef
end GroundTheory.Heights₂.Heights.Model
