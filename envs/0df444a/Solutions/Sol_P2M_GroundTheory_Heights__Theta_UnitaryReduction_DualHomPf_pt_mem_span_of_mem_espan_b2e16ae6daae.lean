-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_span_of_mem_espan_b2e16ae6daae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:39.905962+00:00
-- url     : https://prove2.me/submissions/d51a5c53-85d4-4b06-b3d5-201b6320bb7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_add__f507844539b5
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_zero__bbddd9770dc5
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_smul__159faebf7988

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
theorem _root_.solution (A : Submodule (𝓞 E) S.V) {w : S.V} (hw : w ∈ espan A) :
    S.pt τ w ∈ Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [pt_zero']; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [pt_add']; exact Submodule.add_mem _ hx hy
  | smul e x _ hx => rw [pt_smul']; exact Submodule.smul_mem _ _ hx
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
