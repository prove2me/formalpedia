-- Prove2me | solution 1 for WeightedRootIntegralIdentity.finiteKeyholeResidueLimit
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:46:19.035984+00:00
-- url     : https://prove2.me/submissions/43fc8e8b-89d0-4956-ad85-f02e9577ef6f

import Mathlib
open Filter Topology

theorem solution
    (U L VR VL I O : ℕ → ℂ) (R : ℂ)
    (hfull : Tendsto (fun m : ℕ => U m + L m + VR m + VL m + I m + O m) atTop (𝓝 R))
    (hVR : Tendsto VR atTop (𝓝 0))
    (hVL : Tendsto VL atTop (𝓝 0))
    (hI : Tendsto I atTop (𝓝 0))
    (hO : Tendsto O atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => U m + L m) atTop (𝓝 R) := by
  have h := (((hfull.sub hO).sub hI).sub hVL).sub hVR
  simpa only [add_sub_cancel_right, sub_zero] using h
