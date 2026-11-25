-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.isInt_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:49.762527+00:00
-- url     : https://prove2.me/submissions/a515327c-3f3c-433f-9e52-71676576d50d

import Mathlib
import Definitions.Def_ReciprocityTheory_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_val_R

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
theorem _root_.solution (r : R) : IsInt (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) := by
  intro v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1
  rw [val_R]
  exact v.intValuation_le_one r
end ReciprocityTheory.UG.AdeleIntA
