-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isModelOver_line_c8d82f335840
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:35.694377+00:00
-- url     : https://prove2.me/submissions/88745775-0ee3-46ef-8ffa-d5d2c541c80c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (O)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution : IsModelOver (⊥ : Ideal (MRingOver O (fun _ : Unit => Fin 2))) 1 := by
  refine ⟨⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ⟨0, by simp [X_ne_zero]⟩⟩, ?_, ?_⟩
  · exact Ideal.comap_bot_of_injective _ (MvPolynomial.C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
