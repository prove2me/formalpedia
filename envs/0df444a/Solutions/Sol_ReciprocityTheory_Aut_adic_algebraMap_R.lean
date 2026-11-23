-- Prove2me | solution 1 for ReciprocityTheory.Aut.adic_algebraMap_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:45.762808+00:00
-- url     : https://prove2.me/submissions/44755453-07b6-46b6-bf2f-f9fd4c29e5e1

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace ReciprocityTheory.Aut
theorem _root_.solution (a : R) :
    algebraMap R (v.adicCompletion K) a = algebraMap K (v.adicCompletion K) (algebraMap R K a) := rfl
end ReciprocityTheory.Aut
