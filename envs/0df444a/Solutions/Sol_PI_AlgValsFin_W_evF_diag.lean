-- Prove2me | solution 1 for PI.AlgValsFin.W.evF_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:03.800494+00:00
-- url     : https://prove2.me/submissions/237f4600-11b7-4473-b281-003ae11ddc97

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : evF v (diagUnits L k) = atFin v k :=
  Units.ext rfl
end PI.AlgValsFin.W
