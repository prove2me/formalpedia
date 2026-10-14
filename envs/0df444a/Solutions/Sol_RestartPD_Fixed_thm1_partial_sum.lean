-- Prove2me | solution 1 for RestartPD.Fixed.thm1_partial_sum
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:24:13.651413+00:00
-- url     : https://prove2.me/submissions/b3ddf3b8-0a4c-4328-8d9f-f7a6716fbdc6

import Definitions.Def_RestartPD_Fixed_Algorithms

open RestartPD.Fixed
open scoped BigOperators

theorem solution {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n))
    (Y : Set (Dual m)) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (tstar : ℕ) (htstar : 1 ≤ tstar)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs tstar z zb)
    (N : ℕ) (hind : ∀ k ≤ N, distZ L X Y p (z k) ≤ β ^ k * distZ L X Y p (z 0)) :
    p (z (N + 1) - z 0) ≤ (q + 2) / (1 - β) * distZ L X Y p (z 0) ∧
      z (N + 1) ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0) := by
  have hq : 0 < q + 2 := by linarith [h3.1]
  have hz (k : ℕ) : z k ∈ X ×ˢ Y := by
    induction k with
    | zero => exact hz0
    | succ k ih =>
      rw [(hrun k).2]
      exact (h3.2.2 (z k) ih (zb k) (hrun k).1 tstar htstar).1
  have hstep (k : ℕ) : p (z (k + 1) - z k) ≤ (q + 2) * distZ L X Y p (z k) := by
    rw [(hrun k).2]
    exact (h3.2.2 (z k) (hz k) (zb k) (hrun k).1 tstar htstar).2.2
  have hd : 0 ≤ distZ L X Y p (z 0) := by
    exact (mul_nonneg_iff_of_pos_left hq).mp ((apply_nonneg p _).trans (hstep 0))
  have hsum (t : ℕ) :
      p (z t - z 0) ≤ ∑ k ∈ Finset.range t, p (z (k + 1) - z k) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have he : z (t + 1) - z 0 = (z (t + 1) - z t) + (z t - z 0) := by abel
      rw [he, Finset.sum_range_succ]
      exact (map_add_le_add p _ _).trans (by linarith)
  have hg : ∑ k ∈ Finset.range (N + 1), β ^ k ≤ 1 / (1 - β) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) hβ.1.le hβ.2)
  have hbound : p (z (N + 1) - z 0) ≤ (q + 2) / (1 - β) * distZ L X Y p (z 0) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), p (z (k + 1) - z k) := hsum (N + 1)
      _ ≤ ∑ k ∈ Finset.range (N + 1), (q + 2) * (β ^ k * distZ L X Y p (z 0)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hstep k).trans (mul_le_mul_of_nonneg_left (hind k (by
          have := Finset.mem_range.mp hk
          omega)) hq.le)
      _ = ((q + 2) * distZ L X Y p (z 0)) * ∑ k ∈ Finset.range (N + 1), β ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ((q + 2) * distZ L X Y p (z 0)) * (1 / (1 - β)) :=
        mul_le_mul_of_nonneg_left hg (mul_nonneg hq.le hd)
      _ = _ := by ring
  refine ⟨hbound, hz (N + 1), ?_⟩
  have hsymm : p (z 0 - z (N + 1)) = p (z (N + 1) - z 0) := by
    simpa only [neg_sub] using (map_neg_eq_map p (z (N + 1) - z 0))
  simpa only [hsymm] using hbound
