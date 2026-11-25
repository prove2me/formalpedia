-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.isInt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:54.484839+00:00
-- url     : https://prove2.me/submissions/f37576cf-e5db-482e-baa8-dbca0597acd5

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
theorem _root_.solution {x y : FiniteAdeleRing R K} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) :=
  fun v => add_mem (hx v) (hy v)
end ReciprocityTheory.UG.AdeleIntA
