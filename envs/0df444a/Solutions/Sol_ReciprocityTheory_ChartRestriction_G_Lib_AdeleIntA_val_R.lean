-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.val_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:55.666804+00:00
-- url     : https://prove2.me/submissions/95ccc0b7-828d-4c35-aee3-98a2c3f447f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
private theorem val_R_lemma (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  first
  | exact (valuedAdicCompletion_eq_valuation (K := K) v r).trans (by rw [valuation_of_algebraMap])
  | exact (valuedAdicCompletion_eq_valuation' (R := R) v (algebraMap R K r)).trans
      (by rw [valuation_of_algebraMap])
  | (rw [← IsScalarTower.algebraMap_apply R K (v.adicCompletion K)];
      exact (valuedAdicCompletion_eq_valuation (K := K) v r).trans (by rw [valuation_of_algebraMap]))
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
theorem _root_.solution (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := val_R_lemma v r
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
