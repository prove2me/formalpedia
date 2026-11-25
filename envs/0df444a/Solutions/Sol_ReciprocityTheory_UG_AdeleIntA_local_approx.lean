-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.local_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:40:16.725354+00:00
-- url     : https://prove2.me/submissions/2cf7bb20-3fd4-43f0-be10-7ce6bcb11d2d

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
theorem _root_.solution (v : HeightOneSpectrum R) (x : v.adicCompletion K) (hx : Valued.v x ≤ 1) (m : R) (hm : m ≠ 0) :
    ∃ a : R, Valued.v (x - algebraMap K (v.adicCompletion K) (algebraMap R K a)) < v.intValuation m := by
  have hm0 : v.intValuation m ≠ 0 := v.intValuation_ne_zero m hm
  set γ : (ℤᵐ⁰)ˣ := Units.mk0 _ hm0
  set M : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K m)
  have hM : Valued.v M = v.intValuation m := val_R v m
  have hMne : M ≠ 0 := fun h => hm0 (by rw [← hM, h, map_zero])
  have hM0 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict M ≠ 0 := by
    simpa using hMne
  have hball : {z : v.adicCompletion K | Valued.v (z - x) < Valued.v M} ∈ nhds x :=
    (Valued.mem_nhds).2 ⟨Units.mk0 _ hM0, fun z hz => by
      simpa using (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict_lt_iff.mp hz⟩
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := K) v).mem_nhds hball
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - x) < v.intValuation m := hM ▸ hk
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have e : (k : v.adicCompletion K) = (algebraMap K (v.adicCompletion K) k - x) + x := by
      rw [sub_add_cancel]; rfl
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ hx)
    exact hk'.le.trans (v.intValuation_le_one m)
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := K) v hk1 γ
  refine ⟨a, ?_⟩
  have e : x - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      -(algebraMap K (v.adicCompletion K) k - x) - algebraMap K (v.adicCompletion K) (algebraMap R K a - k) := by
    rw [map_sub]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_neg]; exact hk'
  · have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (algebraMap R K a - k)
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a - k)) = _ at this
    rw [this]
    exact ha
end ReciprocityTheory.UG.AdeleIntA
