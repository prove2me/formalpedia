-- Prove2me | solution 1 for PI.AlgValsFin.W.evI_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:15.716904+00:00
-- url     : https://prove2.me/submissions/7034fa6c-d954-4bc1-815d-bbaaa9f7c07e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (w : InfinitePlace L) (k : Lˣ) : evI w (diagUnits L k) = atInf w k :=
  Units.ext rfl
end PI.AlgValsFin.W
