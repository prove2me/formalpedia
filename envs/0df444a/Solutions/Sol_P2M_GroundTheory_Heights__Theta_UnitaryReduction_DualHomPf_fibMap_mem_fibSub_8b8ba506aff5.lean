-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_mem_fibSub_8b8ba506aff5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:28.874187+00:00
-- url     : https://prove2.me/submissions/32c02367-fdac-4c1c-8412-2394514fc513

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_span_pt_a44c8735491c
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_pt__4ddfecfe2e3e

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
theorem _root_.solution (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (W : Submodule E T.V)
    (hφ : ∀ v, φ v ∈ W) (y : S.FibSp τ) : S.fibMap T φ τ y ∈ T.fibSub W τ := by
  rw [fibSub_eq_span]
  induction mem_span_pt S τ y using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [fibMap_pt']; exact Submodule.subset_span ⟨φ v, hφ v, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
