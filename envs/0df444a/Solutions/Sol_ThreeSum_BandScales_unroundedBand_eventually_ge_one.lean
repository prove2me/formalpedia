-- Prove2me | solution 1 for ThreeSum.BandScales.unroundedBand_eventually_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:12.805546+00:00
-- url     : https://prove2.me/submissions/e9b72413-8b9c-43e4-9ad8-b9b9d7770c03

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_unroundedBand_pos
import Theorems.Thm_ThreeSum_BandScales_unroundedBand_log_rate
import Theorems.Thm_ThreeSum_Parameters_E_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution : ∀ᶠ n : ℕ in atTop, 1 ≤ unroundedBand n := by
  have hpos : (0 : ℝ) < (Parameters.E - 1 / 20) / 5 := by have := Parameters.E_bounds.1; linarith
  have hs := unroundedBand_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (unroundedBand n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (unroundedBand_pos n).le).mp hb).le
end ThreeSum.BandScales
