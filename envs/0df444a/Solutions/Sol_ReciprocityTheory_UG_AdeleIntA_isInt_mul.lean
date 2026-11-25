-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.isInt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:40:06.92288+00:00
-- url     : https://prove2.me/submissions/f0bd2376-0049-4504-bd6a-f270c1c22e02

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
theorem _root_.solution {x y : FiniteAdeleRing R K} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) :=
  fun v => mul_mem (hx v) (hy v)
end ReciprocityTheory.UG.AdeleIntA
