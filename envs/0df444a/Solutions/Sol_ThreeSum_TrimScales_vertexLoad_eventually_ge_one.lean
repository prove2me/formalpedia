-- Prove2me | solution 1 for ThreeSum.TrimScales.vertexLoad_eventually_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:44.637546+00:00
-- url     : https://prove2.me/submissions/6af807de-3f3d-4415-9c03-309b71eed4de

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_vertexLoad_pos
import Theorems.Thm_ThreeSum_TrimScales_vertexLoad_log_rate
import Definitions.Def_WeightedCache3SUM_Alias_e0e7cfdb7f4c8115


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution : ∀ᶠ h : ℕ in atTop, 1 ≤ vertexLoad h := by
  have hpos : 0 < Parameters.kappa / 2 := by have := Parameters.kappa_positive; linarith
  have hr := vertexLoad_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hr, eventually_ge_atTop (1 : ℕ)] with h hh hhpos
  have hhp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
  have hlog : 0 < Real.log (vertexLoad h) := (div_pos_iff.mp hh).elim
    (fun hp => hp.1) (fun hp => False.elim (not_lt_of_ge hden.le hp.2))
  exact (Real.log_pos_iff (vertexLoad_pos h).le).mp hlog |>.le
end ThreeSum.TrimScales
