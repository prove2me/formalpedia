-- Prove2me | solution 1 for PI.AlgValsFin.W.evI_infIdele_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:19.254384+00:00
-- url     : https://prove2.me/submissions/fd0e9ad4-615d-46d9-b1e5-93cf468da189

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_ne


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
theorem _root_.solution (w w' : InfinitePlace L) (h : w' ≠ w) (x : (w.Completion)ˣ) :
    evI w' (infIdele L w x) = 1 :=
  Units.ext (infIdele_fst_ne L w w' h x)
end PI.AlgValsFin.W
