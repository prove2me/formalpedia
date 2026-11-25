-- Prove2me | solution 1 for PI.AlgValsFin.W.val_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:18:51.895352+00:00
-- url     : https://prove2.me/submissions/904bb14b-54fc-437c-aad1-0ddb76ca3499

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace PI.AlgValsFin.W
theorem _root_.solution (y : L) : Valued.v (algebraMap L (v.adicCompletion L) y) = v.valuation L y := by
  exact valuedAdicCompletion_eq_valuation' v y
end PI.AlgValsFin.W
