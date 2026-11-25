-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_span_pt_a44c8735491c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:56.074794+00:00
-- url     : https://prove2.me/submissions/399c06dd-4096-4acc-9533-bedece133d97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_tmul_eq_smul_pt_5df8628f0614

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
theorem _root_.solution (y : S.FibSp τ) : y ∈ Submodule.span ℂ (Set.range (S.pt τ)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul z v =>
    rw [tmul_eq_smul_pt]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add y y' hy hy' => exact Submodule.add_mem _ hy hy'
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
