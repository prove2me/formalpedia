-- Prove2me | solution 1 for PI.AlgValsFin.W.evF_infDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:23.267476+00:00
-- url     : https://prove2.me/submissions/de1be726-e82c-4987-97f0-212d12976bc7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Theorems.Thm_PI_AlgValsFin_W_evF_infIdele

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : evF v (infDiag k) = 1 := by
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => evF_infIdele v w _
end PI.AlgValsFin.W
