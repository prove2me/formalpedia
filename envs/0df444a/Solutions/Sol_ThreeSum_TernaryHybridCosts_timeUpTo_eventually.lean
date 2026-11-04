-- Prove2me | solution 1 for ThreeSum.TernaryHybridCosts.timeUpTo_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:41.391075+00:00
-- url     : https://prove2.me/submissions/7c38dc52-a9ee-46d7-ab1d-0a89b6d4c6f7

import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Theorems.Thm_ThreeSum_TernaryHybridCosts_time_eventually_uniform
import Theorems.Thm_ThreeSum_TernaryEndBridge_timeUpTo_eventually_of_uniform


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCosts
open Light StageBounds Filter
noncomputable section
namespace ThreeSum.TernaryHybridCosts
theorem _root_.solution {T : ℕ → ℕ} {a b : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (hab : a < b) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (TernaryHybridCore.time T κ cutoff) n ((n : ℝ)^(κ : ℝ)) ≤
        (n : ℝ)^b :=
  TernaryEndBridge.timeUpTo_eventually_of_uniform
    (time_eventually_uniform hT ha hab κ cutoff)
end ThreeSum.TernaryHybridCosts
