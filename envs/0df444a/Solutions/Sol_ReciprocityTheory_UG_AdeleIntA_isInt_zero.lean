-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.isInt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:40:13.139888+00:00
-- url     : https://prove2.me/submissions/82f628bc-10f5-45f3-b48d-f37895583766

import Mathlib
import Definitions.Def_ReciprocityTheory_AdeleApproximation_AdeleIntA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain WithZero
open ReciprocityTheory ReciprocityTheory.UG ReciprocityTheory.UG.AdeleIntA
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace ReciprocityTheory.UG.AdeleIntA
theorem _root_.solution : IsInt (0 : FiniteAdeleRing R K) := fun v => zero_mem (v.adicCompletionIntegers K)
end ReciprocityTheory.UG.AdeleIntA
