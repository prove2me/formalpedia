-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_tmul_eq_smul_pt_5df8628f0614
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:06:59.181923+00:00
-- url     : https://prove2.me/submissions/ca2fe59b-28b4-4983-b4ed-fea644e0567e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers

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
theorem _root_.solution (z : CAt τ.embedding) (v : S.V) :
    (z ⊗ₜ[E] v : S.FibSp τ) = (CAt.ofComplex τ.embedding).symm z • S.pt τ v := by
  change z ⊗ₜ[E] v = (CAt.ofComplex τ.embedding).symm z • ((1 : CAt τ.embedding) ⊗ₜ[E] v)
  rw [TensorProduct.smul_tmul', CAt.complex_smul_def, AlgEquiv.apply_symm_apply, mul_one]
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
