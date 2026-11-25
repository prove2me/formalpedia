-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_of_atPrime_042fe231d9ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:14.405052+00:00
-- url     : https://prove2.me/submissions/75d60735-94a9-418b-8605-493f4dfe6512

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
theorem _root_.solution {B C : Type*} [CommRing B] [CommRing C] [Algebra B C] (𝔪 : Ideal B) [𝔪.IsPrime]
    [IsLocalization.AtPrime C 𝔪] (ρ : C →+* Ω) (hker : ∀ b, ρ (algebraMap B C b) = 0 ↔ b ∈ 𝔪) (S : Subfield Ω)
    (hS : ∀ b, ρ (algebraMap B C b) ∈ S) (z : C) : ρ z ∈ S := by
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl z
  have e := congrArg ρ (IsLocalization.mk'_spec C b t)
  rw [map_mul] at e
  have ht : ρ (algebraMap B C t) ≠ 0 := fun h => t.2 ((hker t).1 h)
  rw [eq_div_of_mul_eq ht e]
  exact div_mem (hS b) (hS t)
end GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
