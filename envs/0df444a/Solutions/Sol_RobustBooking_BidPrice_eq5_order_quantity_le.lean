-- Prove2me | solution 1 for RobustBooking.BidPrice.eq5_order_quantity_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:48:32.673587+00:00
-- url     : https://prove2.me/submissions/03288c12-a088-4bef-b19b-e7f7e9c3fa64

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

open RobustBooking.BidPrice in
theorem solution (fmin fmax : ℝ) (Q : ℝ → ℝ) (f : ℝ) (hf : f ∈ Set.Icc fmin fmax) :
    orderQuantityControl fmin fmax Q (Q f) ≤ f := by
  unfold orderQuantityControl
  apply csInf_le
  · exact ⟨fmin, fun g hg => hg.1.1⟩
  · exact ⟨hf, le_rfl⟩
