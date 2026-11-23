-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.tau_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:57.695337+00:00
-- url     : https://prove2.me/submissions/e09d7c45-8d7d-498a-9f16-5671a019b9bc

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (c : E) :
    τ (star c * c) = (Complex.normSq (τ c) : ℂ) := by
  rw [map_mul, hstar, Complex.normSq_eq_conj_mul_self]
end PI.AutLzFinite.SlopeTestRemainingChoices
