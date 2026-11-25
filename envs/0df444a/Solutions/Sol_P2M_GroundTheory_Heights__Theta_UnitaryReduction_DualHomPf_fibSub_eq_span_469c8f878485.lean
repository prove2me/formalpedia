-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:53.349453+00:00
-- url     : https://prove2.me/submissions/8a727474-6745-4702-8456-ee70b9d86831

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
theorem _root_.solution (W : Submodule E S.V) :
    S.fibSub W τ = Submodule.span ℂ (S.pt τ '' (W : Set S.V)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z w =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      have hmem : S.pt τ (w : S.V) ∈ Submodule.span ℂ (S.pt τ '' (W : Set S.V)) :=
        Submodule.subset_span ⟨w, w.2, rfl⟩
      have h2 := (Submodule.span ℂ (S.pt τ '' (W : Set S.V))).smul_mem
        ((CAt.ofComplex τ.embedding).symm z) hmem
      rw [← tmul_eq_smul_pt] at h2
      exact h2
    | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(1 : CAt τ.embedding) ⊗ₜ[E] (⟨w, hw⟩ : W), by
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]; rfl⟩
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
