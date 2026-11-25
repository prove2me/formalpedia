-- Prove2me | solution 1 for PI.AlgValsFin.W.evF_infIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:09.108875+00:00
-- url     : https://prove2.me/submissions/ef32f54c-983a-492c-ad54-84cb1507d667

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_snd


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    evF v (infIdele L w x) = 1 :=
  Units.ext (infIdele_snd L w x v)
end PI.AlgValsFin.W
