-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.val_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:42.269477+00:00
-- url     : https://prove2.me/submissions/66452eec-a002-48e7-8d5d-6e0813f0462b

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
theorem _root_.solution (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  have h := v.valuedAdicCompletion_eq_valuation' (algebraMap R K r)
  rw [v.valuation_of_algebraMap] at h
  exact h
end ReciprocityTheory.UG.AdeleIntA
