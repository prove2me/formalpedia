-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.pmu_nonneg_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:08:24.028835+00:00
-- url     : https://prove2.me/submissions/83fe5cd2-89dc-499f-be98-89266e6b2bc7

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_pm_factorization

namespace ProjSelfConcordant.ConicExt.ConcavityProof

lemma between_endpoints (ν μ a t : ℝ) (ha : 0 ≤ a) (hμ : |μ| ≤ a)
    (hplus : 0 ≤ pmu ν a t) (hminus : 0 ≤ pmu ν (-a) t) : 0 ≤ pmu ν μ t := by
  have hm := abs_le.mp hμ
  have hs : μ ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) (by linarith : 0 ≤ a + μ)]
  by_cases hc : 0 ≤ 4 * t ^ 3 + 12 * t
  · have hi : pmu ν μ t - pmu ν (-a) t =
        (μ + a) * (4 * t ^ 3 + 12 * t) + (a ^ 2 - μ ^ 2) := by
      unfold pmu
      ring
    have hp : 0 ≤ (μ + a) * (4 * t ^ 3 + 12 * t) := mul_nonneg (by linarith) hc
    linarith
  · have hi : pmu ν μ t - pmu ν a t =
        (μ - a) * (4 * t ^ 3 + 12 * t) + (a ^ 2 - μ ^ 2) := by
      unfold pmu
      ring
    have hp : 0 ≤ (μ - a) * (4 * t ^ 3 + 12 * t) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (le_of_not_ge hc)
    linarith

lemma sqrt_parameters (ν : ℝ) (hν : 2 ≤ ν) :
    1 ≤ Real.sqrt (ν - 1) ∧ (Real.sqrt (ν - 1)) ^ 2 + 1 = ν ∧
      2 * ((Real.sqrt (ν - 1)) ^ 2 - 1) / Real.sqrt (ν - 1) =
        2 * ((ν - 2) / Real.sqrt (ν - 1)) := by
  have hn : 0 ≤ ν - 1 := by linarith
  have hs : (Real.sqrt (ν - 1)) ^ 2 = ν - 1 := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg (ν - 1)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · linarith
  · rw [hs]
    ring

end ProjSelfConcordant.ConicExt.ConcavityProof

open ProjSelfConcordant.ConicExt

theorem solution (ν μ : ℝ) (hν : 2 ≤ ν)
    (hμ : |μ| ≤ 2 * ((ν - 2) / Real.sqrt (ν - 1))) :
    ∀ t : ℝ, 0 ≤ pmu ν μ t := by
  intro t
  obtain ⟨hk, heq, hc⟩ := ConcavityProof.sqrt_parameters ν hν
  have h := pmu_pm_factorization (Real.sqrt (ν - 1)) t hk
  have hp : 0 ≤ pmu ν (2 * ((ν - 2) / Real.sqrt (ν - 1))) t := by
    simpa only [heq, hc] using h.2.2.1
  have hm : 0 ≤ pmu ν (-(2 * ((ν - 2) / Real.sqrt (ν - 1)))) t := by
    simpa only [heq, hc] using h.2.2.2
  exact ConcavityProof.between_endpoints ν μ _ t ((abs_nonneg μ).trans hμ) hμ hp hm
