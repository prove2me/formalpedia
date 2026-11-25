-- Prove2me | solution 1 for PI.AlgValsFin.W.prod_mem_compo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:23.054539+00:00
-- url     : https://prove2.me/submissions/6ca6994d-4b49-49fc-9aa7-f5beb1c5ab70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
import Theorems.Thm_PI_AlgValsFin_W_mem_compo

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
theorem _root_.solution (m : (L →+* ℂ) → ℤ) (k : L) : ∏ φ : L →+* ℂ, φ k ^ m φ ∈ compo L :=
  prod_mem fun φ _ => zpow_mem (mem_compo φ k) _
end PI.AlgValsFin.W
