-- Prove2me | solution 1 for OnlinePrimalDual.AdAuctions.allocation_competitive_ratio
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:55:26.190655+00:00
-- url     : https://prove2.me/submissions/40abe602-147d-4452-8cad-df54ff5407aa

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue
import Definitions.Def_OnlinePrimalDual_AdAuctions_actualCharge

namespace OnlinePrimalDual.AdAuctions

/-- One buyer, one item, budget `1`, bid `1/2`, `Rmax = 1/2`. -/
noncomputable def aux_acr_inst : AdAuctionsInstance Unit Unit where
  b := fun _ _ => 1 / 2
  hb_nonneg := fun _ _ => by norm_num
  B := fun _ => 1
  hB_pos := fun _ => by norm_num
  Rmax := 1 / 2
  hRmax_pos := by norm_num
  hRmax_bound := fun _ _ => by norm_num

lemma aux_acr_cParam : cParam aux_acr_inst = 9 / 4 := by
  unfold cParam
  show (1 + (1 / 2 : ℝ)) ^ (1 / (1 / 2 : ℝ)) = 9 / 4
  have h : (1 / (1 / 2 : ℝ)) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h, Real.rpow_natCast]
  norm_num

end OnlinePrimalDual.AdAuctions

open OnlinePrimalDual.AdAuctions

theorem solution : ¬ (∀ {I M : Type} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (wonBids : I → List ℝ)
    (hbids_valid : ∀ i, ∀ bd ∈ wonBids i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i)
    (h_dual_near_feasible : ∀ i : I, buyerX inst i (wonBids i) ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ (revenue inst wonBids i / inst.B i) - 1))
    (h_at_most_one_undercharge : ∀ i : I,
      revenue inst wonBids i ≤ inst.B i * (1 + inst.Rmax)),
    ∀ y'' : I → M → ℝ, (∀ i j, 0 ≤ y'' i j) →
      (∀ j, ∑ i, y'' i j ≤ 1) →
      (∀ i, ∑ j, inst.b i j * y'' i j ≤ inst.B i) →
      ∑ i, actualCharge inst wonBids i ≥
        (1 - 1 / cParam inst) * (1 - inst.Rmax) *
          (∑ i, ∑ j, inst.b i j * y'' i j)) := by
  intro h
  have key := h aux_acr_inst (fun _ => [])
    (fun _ bd hbd => by simp at hbd)
    (fun _ => by
      simp [buyerX, revenue])
    (fun _ => by
      simp only [revenue, List.sum_nil]
      show (0 : ℝ) ≤ 1 * (1 + 1 / 2)
      norm_num)
    (fun _ _ => 1) (fun _ _ => by norm_num)
    (fun _ => by simp)
    (fun _ => by
      simp only [Finset.univ_unique, Finset.sum_singleton, mul_one]
      show (1 / 2 : ℝ) ≤ 1
      norm_num)
  rw [aux_acr_cParam] at key
  simp only [actualCharge, revenue, List.sum_nil, Finset.univ_unique,
    Finset.sum_singleton, mul_one] at key
  change min (0 : ℝ) 1 ≥ (1 - 1 / (9 / 4)) * (1 - 1 / 2) * (1 / 2) at key
  norm_num at key
