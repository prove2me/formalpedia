-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_mode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:26.981347+00:00
-- url     : https://prove2.me/submissions/171353d2-30bd-4a68-90cf-5297a6ec4855

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_step_up
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_step_down

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k j : ℕ} (hk : k < n) : weight n k j ≤ weight n k k := by
  by_cases hj : j ≤ k
  · have hu : ∀ {a b : ℕ}, a ≤ b → b ≤ k → weight n k a ≤ weight n k b := by
      intro a b hab
      induction hab with
      | refl => intro _; exact le_rfl
      | @step b hab ih =>
          intro hbk
          exact (ih (by omega)).trans (weight_step_up hk (by omega))
    exact hu hj le_rfl
  · have hd : AntitoneOn (weight n k) {i | k ≤ i} :=
      antitoneOn_nat_Ici_of_succ_le (fun i hi => weight_step_down hk hi)
    have hkj : k ≤ j := by omega
    exact hd (a := k) (by simp) (b := j) hkj hkj
end ThreeSum.BinomialEntropy
