-- Prove2me | solution 1 for PI.AlgValsFin.W.isIntegral_of_mem_compo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:04.385036+00:00
-- url     : https://prove2.me/submissions/a56694df-bd7a-4243-b06f-32f3aac160e8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution {y : ℂ} (hy : y ∈ compo L) : IsIntegral ℚ y := by
  have h := (IsIntegral.of_finite ℚ (⟨y, hy⟩ : compo L)).map (compo L).val
  exact h
end PI.AlgValsFin.W
