-- Prove2me | solution 1 for SkipFreeFluct.MBI.theorem_5_4_calH_mbp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:29:58.168374+00:00
-- url     : https://prove2.me/submissions/24dadc14-f8c8-4e0d-92f8-9be423d4238e

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

open SkipFreeFluct.MBI Finset in
theorem solution (P : MBIParams) :
    IsMBP P → ∀ x y : ℕ, calH P y x = Wz P ((y : ℤ) - x - 1) / y := by
  rintro ⟨hb, hq⟩ x y
  have hk : ∀ k, kappa P k = 0 := fun k => by simp [kappa, hb, hq]
  have hpi : ∀ k, piSeq P (k + 1) = 0 := fun k => by
    rw [piSeq]; simp [hk]
  have hvp : ∀ k, varpi P (k + 1) = 0 := fun k => by
    rw [varpi]; simp [hk]
  have hpi' : ∀ k, piSeq P k = if k = 0 then 1 else 0 := by
    intro k; cases k with
    | zero => simp [piSeq]
    | succ k => simp [hpi]
  have hconv : ∀ l, conv (W P) (varpi P) l = W P l := by
    intro l
    unfold conv
    rw [Finset.sum_eq_single 0]
    · simp [varpi]
    · intro j _ hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      simp [hvp]
    · intro h; simp at h
  unfold calH
  simp_rw [hconv, hpi']
  rcases Nat.lt_or_ge x y with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, y = x + n + 1 := ⟨y - x - 1, by omega⟩
    rw [Finset.sum_eq_single n]
    · have h1 : x + n + 1 - x - 1 - n = 0 := by omega
      have h2 : ((x + n + 1 : ℕ) : ℤ) - x - 1 = (n : ℤ) := by push_cast; ring
      rw [h1, h2]
      simp [Wz]
      congr 1; push_cast; ring
    · intro l hl hln
      have : x + n + 1 - x - 1 - l ≠ 0 := by
        have := Finset.mem_range.1 hl; omega
      simp [this]
    · intro hn; exfalso; apply hn; simp; omega
  · have : y - x = 0 := by omega
    rw [this]
    have h2 : (y : ℤ) - x - 1 < 0 := by omega
    simp [Wz, h2]
