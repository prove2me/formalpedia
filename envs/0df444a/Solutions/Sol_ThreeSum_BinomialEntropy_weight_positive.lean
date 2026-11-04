-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:22.981806+00:00
-- url     : https://prove2.me/submissions/49113e87-7f9c-4431-8288-dda39394cf23

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    0 < weight n k k := by
  have hc : 0 < n.choose k := Nat.choose_pos hk.le
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  unfold weight
  positivity
end ThreeSum.BinomialEntropy
