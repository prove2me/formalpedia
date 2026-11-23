-- Prove2me | solution 1 for PI.LPI.adOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:58.443399+00:00
-- url     : https://prove2.me/submissions/34abaed6-5268-454b-a9e9-06671aca526e

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
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : adOf a ha ∈ intAd F := fun v => ha v
end PI.LPI
