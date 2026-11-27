-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.isInt_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:26:58.025649+00:00
-- url     : https://prove2.me/submissions/62b91539-98ea-4b21-b713-e7a549eb65ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_int_R
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
private theorem algK_apply_lemma_2 (v : HeightOneSpectrum R) (k : K) :
    (algebraMap K (FiniteAdeleRing R K) k) v = algebraMap K (v.adicCompletion K) k := by
  first
  | rfl
  | (simp; done)
private theorem algR_apply_lemma_3 (v : HeightOneSpectrum R) (r : R) :
    (algebraMap R (FiniteAdeleRing R K) r) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) := by
  first
  | rfl
  | (rw [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K)]; exact algK_apply_lemma_2 v _)
  | (simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]; done)
  | (simp [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K)]; done)
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
theorem _root_.solution (r : R) : IsInt (algebraMap R (FiniteAdeleRing R K) r) := by
  intro v
  rw [algR_apply_lemma_3]
  exact int_R v r
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
