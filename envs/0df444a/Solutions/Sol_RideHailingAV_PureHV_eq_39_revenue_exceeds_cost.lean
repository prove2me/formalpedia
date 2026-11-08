-- Prove2me | solution 1 for RideHailingAV.PureHV.eq_39_revenue_exceeds_cost
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:42:08.892694+00:00
-- url     : https://prove2.me/submissions/18ff7cd5-6e5c-4fed-8708-5d9aad0b651e

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_revenue
import Definitions.Def_RideHailingAV_PureHV_laborCost

open RideHailingAV.PureHV in
theorem solution (M : Market) (ht2 : 0 < M.t2) (hV : 0 < M.V)
    (m m' : ℝ) (hm : 0 < m) (hmm' : m < m') (d : ℝ) (hd : 0 < d) (hdm : d ≤ m)
    (heq : revenue M m d = laborCost M d) :
    laborCost M d < revenue M m' d := by
  rw [← heq]
  unfold revenue invDemand
  have hm' : 0 < m' := lt_trans hm hmm'
  have hlt : d / m' < d / m := div_lt_div_of_pos_left hd hm hmm'
  have hk : 0 < d * M.V * M.t2 := by positivity
  nlinarith [mul_lt_mul_of_pos_left hlt hk]
