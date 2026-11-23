-- Prove2me | solution 1 for ReciprocityTheory.Aut.adic_valued_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:56.4354+00:00
-- url     : https://prove2.me/submissions/734aa448-8238-495c-b059-9e6ffcc4aca2

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
theorem _root_.solution (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  valuedAdicCompletion_eq_valuation' v k
end ReciprocityTheory.Aut
