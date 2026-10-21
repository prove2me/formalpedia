-- Prove2me | solution 1 for RetailVariety.Statics.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:21:56.193146+00:00
-- url     : https://prove2.me/submissions/f9477064-09e6-4516-a671-ccac842821e5

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model
set_option autoImplicit false
open Filter Topology
open RetailVariety.Statics

theorem solution (n i : ℕ) (hin : i < n) (v : Fin n → ℝ) (v0 p c lam : ℝ) (hlam : 0 < lam) :
    (RetailVariety.Structure.profitT p c lam v v0 (A n i) ≤ RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) ↔
      ∑ j ∈ A n i, max (p * RetailVariety.Structure.share v v0 (A n i) j - c) 0
        ≤ ∑ j ∈ A n (i + 1), max (p * RetailVariety.Structure.share v v0 (A n (i + 1)) j - c) 0) ∧
    (RetailVariety.Structure.profitT p c lam v v0 (A n i) < RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) ↔
      ∑ j ∈ A n i, max (p * RetailVariety.Structure.share v v0 (A n i) j - c) 0
        < ∑ j ∈ A n (i + 1), max (p * RetailVariety.Structure.share v v0 (A n (i + 1)) j - c) 0) := by
  have key : ∀ S : Finset (Fin n), RetailVariety.Structure.profitT p c lam v v0 S =
      (∑ j ∈ S, max (p * RetailVariety.Structure.share v v0 S j - c) 0) * lam := by
    intro S
    unfold RetailVariety.Structure.profitT
    rw [Finset.sum_mul]
  rw [key, key]
  exact ⟨mul_le_mul_iff_left₀ hlam, mul_lt_mul_iff_left₀ hlam⟩
