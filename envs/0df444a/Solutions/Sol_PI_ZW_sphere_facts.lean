-- Prove2me | solution 1 for PI.ZW.sphere_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:30.530895+00:00
-- url     : https://prove2.me/submissions/0ac71f5d-3fd9-4feb-ac3b-23eb09ad7040

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution {z : ℂ} {t : ℝ} (hz : z ∈ sphere (2 + t * I) (19 / 10)) :
    1 / 10 ≤ z.re ∧ ‖z‖ ≤ |t| + 4 := by
  rw [mem_sphere, dist_eq_norm] at hz
  have hc : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  constructor
  · have h1 := Complex.abs_re_le_norm (z - (2 + t * I))
    rw [hz] at h1
    simp at h1
    linarith [(abs_le.mp h1).1]
  · calc ‖z‖ = ‖(z - (2 + t * I)) + (2 + t * I)‖ := by ring_nf
      _ ≤ ‖z - (2 + t * I)‖ + ‖(2 : ℂ) + t * I‖ := norm_add_le _ _
      _ ≤ |t| + 4 := by rw [hz]; linarith
end PI.ZW
