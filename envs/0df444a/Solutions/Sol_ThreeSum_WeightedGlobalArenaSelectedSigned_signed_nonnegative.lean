-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.signed_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:04:29.531238+00:00
-- url     : https://prove2.me/submissions/fc613f24-b305-404b-8731-4e12c8fa6988

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_Light_Limits_Addr_abs_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution {x : ℤ} {b : ℕ} (hb : b≤p) (hx : x.natAbs≤b) : 0≤(p : ℤ)+x := by
  have hab : |x|≤(b : ℤ) := by rw [←Int.natCast_natAbs]; exact_mod_cast hx
  have hp : (b : ℤ)≤p := by exact_mod_cast hb
  have hh := (abs_le.mp hab).1
  omega
end ThreeSum.WeightedGlobalArenaSelectedSigned
