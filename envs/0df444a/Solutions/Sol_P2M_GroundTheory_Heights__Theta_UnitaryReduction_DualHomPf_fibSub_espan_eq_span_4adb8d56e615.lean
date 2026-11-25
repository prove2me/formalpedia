-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_espan_eq_span_4adb8d56e615
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:42.644018+00:00
-- url     : https://prove2.me/submissions/9e3d9e64-21dd-4d63-9843-f17cf76211f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_span_of_mem_espan_b2e16ae6daae

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (S : MetSpace E) (τ : InfinitePlace E)
namespace GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
theorem _root_.solution (A : Submodule (𝓞 E) S.V) :
    S.fibSub (espan A) τ = Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by
  rw [fibSub_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨w, hw, rfl⟩; exact pt_mem_span_of_mem_espan S τ A hw
  · exact Submodule.span_mono (Set.image_mono (fun x hx => Submodule.subset_span hx))
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
