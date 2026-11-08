-- Prove2me | solution 1 for RideHailingAV.PureHV.eq_14_price_util_wage
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:07:08.64202+00:00
-- url     : https://prove2.me/submissions/936e6094-6827-4f64-805c-efabd4ab4de5

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_revenue
import Definitions.Def_RideHailingAV_PureHV_laborCost
import Definitions.Def_RideHailingAV_PureHV_util

open RideHailingAV.PureHV in
theorem solution (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r) (hr1 : M.r < 1)
    (ht2 : 0 < M.t2) (m : ℝ) (hm : 0 < m) (d : ℝ) (hd : 0 < d) (hdm : d ≤ m) :
    revenue M m d = laborCost M d ↔ invDemand M m d * util M d = wage M (minSupply M d) := by
  have hle : d * M.t2 ≤ minSupply M d := by
    unfold minSupply
    apply le_csInf (Set.Nonempty.image _ ⟨1, Set.mem_Ioi.mpr one_pos⟩)
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (0 : ℝ) < s := hs
    have hp : 0 < s ^ (-M.r) := Real.rpow_pos_of_pos hs' _
    have h := mul_pos hd (mul_pos ha hp)
    nlinarith
  have hS : 0 < minSupply M d := lt_of_lt_of_le (mul_pos hd ht2) hle
  unfold revenue laborCost util
  rw [show invDemand M m d * (d * M.t2 / minSupply M d)
      = d * invDemand M m d * M.t2 / minSupply M d by ring, div_eq_iff hS.ne']
