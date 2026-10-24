-- Prove2me | solution 1 for PricingWithTips.adjustedValue_store_off_order
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:19:16.93852+00:00
-- url     : https://prove2.me/submissions/f104359d-ab7a-4a7d-97e9-f952351491e5

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem requiredTip_store_decomposition [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    requiredTip M A uBar b s =
      cBS b s + (⨅ d, cDS d s + uBar d) := by
  classical
  have hmap := (OrderIso.addLeft (cBS b s)).map_ciInf
    (Finite.bddBelow_range (fun d : D => cDS d s + uBar d))
  simp only [OrderIso.addLeft_apply] at hmap
  simp only [requiredTip, if_neg hoff]
  simpa only [hcost, add_assoc] using hmap.symm

theorem requiredTip_buyer_decomposition [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    requiredTip M A uBar b s =
      cBS b s + (⨅ d, cDB d b + uBar d) := by
  classical
  have hmap := (OrderIso.addLeft (cBS b s)).map_ciInf
    (Finite.bddBelow_range (fun d : D => cDB d b + uBar d))
  simp only [OrderIso.addLeft_apply] at hmap
  simp only [requiredTip, if_neg hoff]
  simpa only [hcost, add_assoc] using hmap.symm

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - cBS b s - (⨅ d, cDS d s + uBar d) := by
  rw [adjustedValue, requiredTip_store_decomposition M A uBar cBS cDS hcost b s hoff]
  ring

theorem adjustedValue_buyer_off_order [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - cBS b s - (⨅ d, cDB d b + uBar d) := by
  rw [adjustedValue, requiredTip_buyer_decomposition M A uBar cBS cDB hcost b s hoff]
  ring
