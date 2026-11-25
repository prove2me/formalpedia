-- Prove2me | solution 1 for PI.AlgValsFin.W.evI_infDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:04.458853+00:00
-- url     : https://prove2.me/submissions/ff36cca7-355d-4e4c-a338-c65c2c1c6743

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Theorems.Thm_PI_AlgValsFin_W_evI_infIdele_ne
import Theorems.Thm_PI_AlgValsFin_W_evI_infIdele_self

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
theorem _root_.solution (w : InfinitePlace L) (k : Lˣ) : evI w (infDiag k) = atInf w k := by
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact evI_infIdele_self w _
  · intro w' _ hw'
    exact evI_infIdele_ne w' w (Ne.symm hw') _
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.AlgValsFin.W
