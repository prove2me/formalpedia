-- Prove2me | solution 1 for PI.SelfDualLoc.W.ND.hform_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:23.006793+00:00
-- url     : https://prove2.me/submissions/4ae2b96c-dd05-47b7-8b35-e4d3c70ac083

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.SelfDualLoc.W.ND
theorem _root_.solution (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.SelfDualLoc.W.ND
