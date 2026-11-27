-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_hyps_15e71ba9a296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:50.876957+00:00
-- url     : https://prove2.me/submissions/5d20e606-19da-4483-899f-67c38b47eb39

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace SectionNef
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
    ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
      ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
    ((∃ s : MRing (fun _ : Unit => Fin 2) ℚ, IsMultiHomog s (fun _ => 1) ∧ s ∉ (⊥ : Ideal _)) ∨
      (∀ W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ), IsMultiProjPrime W → ⊥ ≤ W →
        ∃ s : MRing (fun _ : Unit => Fin 2) ℚ, IsMultiHomog s (fun _ => 1) ∧ s ∉ W)) := by
  refine ⟨isMultiProjPrime_bot, ?_, Or.inl ⟨X ⟨(), 0⟩, ?_, ?_⟩⟩
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField
        (Field.toIsField ℚ)]
    have hc : Nat.card ((_ : Unit) × Fin 2) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl
  · have h := isWeightedHomogeneous_X ℚ (blockWeight (fun _ : Unit => Fin 2)) ⟨(), 0⟩
    have e : blockWeight (fun _ : Unit => Fin 2) ⟨(), 0⟩ = fun _ => 1 := by
      funext k
      simp [blockWeight]
    rw [e] at h
    exact h
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
end SectionNef
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
