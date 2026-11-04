-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:29.171903+00:00
-- url     : https://prove2.me/submissions/46e9485c-118c-419d-a2c4-8206ae8bb136

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
theorem _root_.solution (n k j : ℕ) : 0 ≤ weight n k j := by
  unfold weight
  positivity
end ThreeSum.BinomialEntropy
