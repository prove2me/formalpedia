-- Prove2me | solution 1 for WeightedRootIntegralIdentity.finiteKeyholeResidueLimitConcrete
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:46:20.041984+00:00
-- url     : https://prove2.me/submissions/61002f37-2131-456b-900c-bb03eba35093

import Mathlib
open scoped BigOperators
open Filter Topology

theorem solution
    (n : ℕ) (w : ℕ → ℝ) (J : ℕ → ℂ)
    (U L VR VL I O : ℕ → ℂ) (res A B : ℂ)
    (hfinite : ∀ m : ℕ,
      U m + L m + VR m + VL m + I m + O m =
        2 * (Real.pi : ℂ) * Complex.I * res)
    (hVR : Tendsto VR atTop (𝓝 0))
    (hVL : Tendsto VL atTop (𝓝 0))
    (hI : Tendsto I atTop (𝓝 0))
    (hO : Tendsto O atTop (𝓝 0))
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 B))
    (hphase : A + B =
      ∑ k ∈ Finset.range (n - 1),
        (2 * Complex.I * (Real.sin
          (Real.pi * ∑ i ∈ Finset.range (k + 1), w i) : ℂ)) * J k) :
    A + B = 2 * (Real.pi : ℂ) * Complex.I * res ∧
      A + B =
        ∑ k ∈ Finset.range (n - 1),
          (2 * Complex.I * (Real.sin
            (Real.pi * ∑ i ∈ Finset.range (k + 1), w i) : ℂ)) * J k := by
  have hsum := ((((hU.add hL).add hVR).add hVL).add hI).add hO
  have hc : Tendsto (fun _ : ℕ => 2 * (Real.pi : ℂ) * Complex.I * res)
      atTop (𝓝 (A + B)) := by
    simpa only [hfinite, add_zero] using hsum
  exact ⟨tendsto_nhds_unique hc tendsto_const_nhds, hphase⟩
