-- Prove2me | solution 1 for PI.AlgValsFin.W.evF_localIdele_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:16.286462+00:00
-- url     : https://prove2.me/submissions/053d0e5e-8630-4db8-acf8-8be57b3a14ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Theorems.Thm_Neutral_B1_localIdele_snd_self


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    evF v (localIdele L v x) = x :=
  Units.ext (localIdele_snd_self L v x)
end PI.AlgValsFin.W
