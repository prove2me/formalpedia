-- Prove2me | solution 1 for ReciprocityTheory.UG.AdeleIntA.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:03.076287+00:00
-- url     : https://prove2.me/submissions/0866f3ae-4a5f-4874-91dc-390c31c9e39d

import Mathlib
import Definitions.Def_ReciprocityTheory_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_val_R
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_val_le_one_of_mem
import Theorems.Thm_ReciprocityTheory_UG_AdeleIntA_local_approx

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
theorem _root_.solution (y : FiniteAdeleRing R K) (hy : ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K)
    (m : R) (hm : m ≠ 0) : ∃ a : R, ∀ v : HeightOneSpectrum R,
      Valued.v (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤ v.intValuation m := by
  classical
  have hfin : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {m}}.Finite := by
    have hne : Ideal.span {m} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
    have := Ideal.finite_factors hne
    exact this
  set S := hfin.toFinset
  choose b hb using fun v : HeightOneSpectrum R => local_approx v (y v) (val_le_one_of_mem (hy v)) m hm
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {m})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => b v)
  refine ⟨a, fun v => ?_⟩
  have hloc := hb v
  by_cases hv : v ∈ S
  · have h1 := ha v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← v.intValuation_eq_exp_neg_multiplicity hm] at h1
    have e : y v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (y v - algebraMap K (v.adicCompletion K) (algebraMap R K (b v))) -
          algebraMap K (v.adicCompletion K) (algebraMap R K (a - b v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le hloc.le ?_)
    rw [val_R]
    exact h1
  · have hv1 : v.intValuation m = 1 := by
      rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      intro hmem
      apply hv
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
    rw [hv1]
    refine (Valuation.map_sub _ _ _).trans (max_le (val_le_one_of_mem (hy v)) ?_)
    rw [val_R]
    exact v.intValuation_le_one a
end ReciprocityTheory.UG.AdeleIntA
