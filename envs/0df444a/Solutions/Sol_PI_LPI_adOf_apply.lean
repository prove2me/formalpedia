-- Prove2me | solution 1 for PI.LPI.adOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:31.605668+00:00
-- url     : https://prove2.me/submissions/2728012d-c1af-4202-8912-5b8afdaf3010

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.LPI
open Formalism.UG
namespace PI.LPI
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    adOf a ha v = a v := rfl
end PI.LPI
