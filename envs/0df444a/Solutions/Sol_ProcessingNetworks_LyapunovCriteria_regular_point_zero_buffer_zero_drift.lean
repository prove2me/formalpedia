-- Prove2me | solution 1 for ProcessingNetworks.LyapunovCriteria.regular_point_zero_buffer_zero_drift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:04:30.768563+00:00
-- url     : https://prove2.me/submissions/4b827be6-599d-4e71-bf53-7d2c7d1901ca

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_RegularPoint

open ProcessingNetworks.LyapunovCriteria in
theorem solution
    {I J K : ℕ} (dat : FluidEquationData I J K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Dh Fh Th Zh t)
    (i : Fin I) (hz : Zh t i = 0) :
    HasDerivAt (fun s => Zh s i) 0 t := by
  have hd : DifferentiableAt ℝ (fun s => Zh s i) t :=
    differentiableAt_pi.mp hreg.2.2.2 i
  have hmin : IsLocalMin (fun s => Zh s i) t := by
    have hev : ∀ᶠ s in nhds t, 0 < s := lt_mem_nhds ht
    filter_upwards [hev] with s hs
    simp only [hz]
    exact hsol.2.1 s hs.le i
  have h0 : deriv (fun s => Zh s i) t = 0 := hmin.deriv_eq_zero
  rw [← h0]
  exact hd.hasDerivAt
