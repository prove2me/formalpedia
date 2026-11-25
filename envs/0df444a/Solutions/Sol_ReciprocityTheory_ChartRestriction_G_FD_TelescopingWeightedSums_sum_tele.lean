-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums.sum_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:31.879625+00:00
-- url     : https://prove2.me/submissions/a7a478cb-6131-428b-9d93-66ffc9a0a942

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TelescopingWeightedSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
open Finset
namespace ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
theorem _root_.solution (f : ℕ → ℝ) {p n : ℕ} (hp : p ≤ n) :
    ∑ i ∈ Ico p n, (f (i + 1) - f i) = f n - f p := by
  induction n, hp using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    ring
end ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
