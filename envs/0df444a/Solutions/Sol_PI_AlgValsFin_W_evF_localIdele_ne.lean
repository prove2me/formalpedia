-- Prove2me | solution 1 for PI.AlgValsFin.W.evF_localIdele_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:14.379466+00:00
-- url     : https://prove2.me/submissions/177198c2-3e9e-4ad5-99c4-36324fe25970

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
theorem _root_.solution (w v : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    evF w (localIdele L v x) = 1 :=
  by classical exact Units.ext (RestrictedProduct.mulSingle_eq_of_ne
    (fun u : HeightOneSpectrum (𝓞 L) => u.adicCompletionIntegers L) (x : v.adicCompletion L) h)
end PI.AlgValsFin.W
