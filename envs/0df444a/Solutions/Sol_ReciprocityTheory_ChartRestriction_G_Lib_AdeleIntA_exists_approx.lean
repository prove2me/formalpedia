-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:20.844794+00:00
-- url     : https://prove2.me/submissions/63027598-d26a-4ca8-a78e-6993d7b29469

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_int_R
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_val_R
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_exists_approx_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
theorem _root_.solution (c : FiniteAdeleRing R K) (hc : IsInt c) (r : R) (hr : r ≠ 0) :
    ∃ a : R, ∀ v, Valued.v (c v - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  classical
  have hT : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr)
  choose a0 ha0 using fun v => exists_approx_local v (c v) (hc v) r hr
  obtain ⟨a, ha⟩ := exists_forall_sub_mem_ideal (s := hT.toFinset) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {r})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a0 v.1)
  refine ⟨a, fun v => ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · have h1 := ha v hv
    rw [← intValuation_le_pow_iff_mem, ← intValuation_eq_exp_neg_multiplicity v hr] at h1
    have e : c v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (c v - algebraMap K _ (algebraMap R K (a0 v))) - algebraMap K _ (algebraMap R K (a - a0 v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le (ha0 v) ?_)
    rw [val_R]; exact h1
  · have h1 : v.intValuation r = 1 := by
      rw [intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hv ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    rw [h1]; exact sub_mem (hc v) (int_R v a)
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
