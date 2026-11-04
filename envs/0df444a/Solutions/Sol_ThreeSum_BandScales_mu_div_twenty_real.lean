-- Prove2me | solution 1 for ThreeSum.BandScales.mu_div_twenty_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:14.002968+00:00
-- url     : https://prove2.me/submissions/cfa967c6-535f-4257-bb31-db021fa889fa

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_mu_multiple_twenty

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : (mu n / 20 : ℕ) = (mu n : ℝ) / 20 := by
  have h := Nat.div_mul_cancel (mu_multiple_twenty n)
  have hr : ((mu n / 20 : ℕ) : ℝ) * 20 = mu n := by exact_mod_cast h
  linarith
end ThreeSum.BandScales
