-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibFun_pt_a0a904ee7637
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:06.821146+00:00
-- url     : https://prove2.me/submissions/10a4faf4-f8cf-4f77-9050-d1222e87432f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_CAt_algebraMap_apply_5dc063ae0e65


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
theorem _root_.solution (σ : S.V →ₗ[E] E) (v : S.V) :
    fibFun S τ σ (S.pt τ v) = τ.embedding (σ v) := by
  change (CAt.ofComplex τ.embedding).symm
    (S.dualCoord τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) ((1 : CAt τ.embedding) ⊗ₜ[E] v)) = _
  rw [dualCoord_tmul_tmul, one_mul, mul_one, CAt.algebraMap_apply, AlgEquiv.symm_apply_apply]
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
