-- Prove2me | solution 1 for RevShareCoord.Competing.revenue_sharing_profit_identities
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:23:45.249988+00:00
-- url     : https://prove2.me/submissions/994ed369-2cbb-4122-93c7-5c3b4cdf7acf

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

open RevShareCoord.Competing Finset in
theorem solution {n : ℕ} (M : Model n) (qI : Fin n → ℝ) (φ : ℝ) :
    (∀ i, retailerProfit M.R φ (fun k => φ * M.wI qI k) qI i =
        φ * retailerProfit M.R 1 (M.wI qI) qI i) ∧
      supplierProfit M.R M.c φ (fun k => φ * M.wI qI k) qI =
        (1 - φ) * systemProfit M.R M.c qI + φ * supplierProfit M.R M.c 1 (M.wI qI) qI := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [retailerProfit]; ring
  · simp only [supplierProfit, systemProfit, sub_self, zero_mul, zero_add,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
