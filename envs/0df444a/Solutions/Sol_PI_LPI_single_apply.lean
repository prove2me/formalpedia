-- Prove2me | solution 1 for PI.LPI.single_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:39.66427+00:00
-- url     : https://prove2.me/submissions/e32cde71-33d7-4dd6-9e86-a0c306f46e8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
import Theorems.Thm_PI_LPI_adOf_apply


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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : single v a ha v = a := by
  classical
  simp [single, adOf_apply]
end PI.LPI
