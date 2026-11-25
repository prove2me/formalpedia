-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_hypotheses_inhabited_6b811562c9e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:00.655081+00:00
-- url     : https://prove2.me/submissions/807907d3-2f08-48a0-b7f0-93f53fb04de0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087
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
namespace SectionNefGenerated
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
      ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
        ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
      ∀ W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ), IsMultiProjPrime W → ⊥ ≤ W →
        ∃ f g : MRing (fun _ : Unit => Fin 2) ℚ,
          IsRegularSection (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) (fun _ => ((1 : ℕ) : ℤ)) f g ∧
          ∃ u v : MRing (fun _ : Unit => Fin 2) ℚ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ (⊥ : Ideal _) := by
  refine ⟨isMultiProjPrime_bot, projectiveLine_dim, fun W hW _ => ?_⟩
  obtain ⟨i, hi⟩ := hW.relevant ()
  have hdeg : IsMultiHomog (MvPolynomial.X ⟨(), i⟩ : MRing (fun _ : Unit => Fin 2) ℚ) (fun _ => 1) := by
    have := MvPolynomial.isWeightedHomogeneous_X ℚ (blockWeight (fun _ : Unit => Fin 2)) ⟨(), i⟩
    have h : blockWeight (fun _ : Unit => Fin 2) ⟨(), i⟩ = fun _ => 1 := by
      funext k
      simp [blockWeight]
    unfold IsMultiHomog
    rw [← h]
    exact this
  refine ⟨MvPolynomial.X ⟨(), i⟩, 1, isRegularSection_form Ideal.isPrime_bot hdeg ?_, 1,
    MvPolynomial.X ⟨(), i⟩, fun h => hW.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), hi, ?_⟩
  · rw [Ideal.mem_bot]
    exact MvPolynomial.X_ne_zero _
  · simp
end SectionNefGenerated
end GroundTheory.Heights₂.Heights.Model
