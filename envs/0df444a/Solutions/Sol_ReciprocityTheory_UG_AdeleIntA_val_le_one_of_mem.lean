-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.val_le_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.289826+00:00
-- url     : https://prove2.me/submissions/5a6779db-97e8-4d7c-87a5-1c94ca5bb27c

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
theorem _root_.solution {v : HeightOneSpectrum R} {x : v.adicCompletion K} (h : x ∈ v.adicCompletionIntegers K) :
    Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers R K v).1 h
end ReciprocityTheory.UG.AdeleIntA
