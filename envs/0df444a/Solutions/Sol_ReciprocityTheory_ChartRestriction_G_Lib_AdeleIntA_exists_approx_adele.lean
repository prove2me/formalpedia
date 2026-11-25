-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:37:23.021914+00:00
-- url     : https://prove2.me/submissions/26d09b4a-d84c-4283-b8dc-3dc8ca72a8a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_den
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_approx
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
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hrb⟩ := exists_den b
  obtain ⟨a, ha⟩ := exists_approx _ hrb r hr
  refine ⟨algebraMap R K a / algebraMap R K r, fun v => ?_⟩
  have hrK : algebraMap R K r ≠ 0 := by
    first
    | exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    | (rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hr)
    | exact fun h => hr ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 := (map_ne_zero _).mpr hrK
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hrv
  have hk' : algebraMap R K r * (algebraMap R K a / algebraMap R K r) = algebraMap R K a := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hrK, mul_one]
  have hc : (algebraMap R (FiniteAdeleRing R K) r * b) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v := by
    rw [show (algebraMap R (FiniteAdeleRing R K) r * b) v =
        (algebraMap R (FiniteAdeleRing R K) r) v * b v from rfl, algR_apply_lemma_3]
  have hsub : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v =
      b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    rw [show (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v =
        b v - (algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v from rfl,
      algK_apply_lemma_2]
  have key : (algebraMap R (FiniteAdeleRing R K) r * b) v -
        algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) *
        (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v := by
    rw [hc, hsub, mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), hk']
  have hv := ha v
  rw [key, map_mul, ← val_R_lemma (K := K) v r] at hv
  show Valued.v ((b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v) ≤ 1
  first
  | exact (mul_le_mul_left₀ h0).mp (by rwa [mul_one])
  | exact le_of_mul_le_mul_left (by rwa [mul_one]) (zero_lt_iff.mpr h0)
  | exact (mul_le_iff_le_one_right (zero_lt_iff.mpr h0)).mp hv
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
