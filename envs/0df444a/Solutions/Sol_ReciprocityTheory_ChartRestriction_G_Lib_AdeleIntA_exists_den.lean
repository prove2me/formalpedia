-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:41.805837+00:00
-- url     : https://prove2.me/submissions/27a73725-3c9d-4707-acff-65fcc945b04f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_int_R
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_den_local
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
theorem _root_.solution (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hfin : {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
    first
    | exact Filter.eventually_cofinite.mp b.2
    | exact b.2
  choose s hs0 hs using fun v => exists_den_local (R := R) (K := K) v (b v)
  refine ⟨∏ w ∈ hfin.toFinset, s w, Finset.prod_ne_zero_iff.mpr fun w _ => hs0 w, ?_⟩
  intro v
  rw [show (algebraMap R (FiniteAdeleRing R K) (∏ w ∈ hfin.toFinset, s w) * b) v =
      (algebraMap R (FiniteAdeleRing R K) (∏ w ∈ hfin.toFinset, s w)) v * b v from rfl,
    algR_apply_lemma_3]
  by_cases hvS : v ∈ hfin.toFinset
  · rw [← Finset.prod_erase_mul _ _ hvS, map_mul, map_mul, mul_assoc]
    exact mul_mem (int_R v _) (hs v)
  · have hb : b v ∈ v.adicCompletionIntegers K := by
      by_contra hc
      exact hvS (hfin.mem_toFinset.mpr hc)
    exact mul_mem (int_R v _) hb
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
