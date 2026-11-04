-- Prove2me | solution 1 for PerishBaseStock.Backlog.ec_29
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:23:03.443124+00:00
-- url     : https://prove2.me/submissions/578534ee-d478-4d5f-bb42-253dbd667817

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PB7Aux
open PerishBaseStock.Backlog

theorem step (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t i : ℕ)
    (hi1 : 1 ≤ i) (hi2 : i ≤ c.m + c.L - 1) :
    levelAt c π d (t + 1) i = levelAt c π d t (i + 1) - (d t : ℝ) - outdatedAt c π d t := by
  have hne : i ≠ c.m + c.L := by omega
  simp only [levelAt, level, if_neg hne, stateCoord, dif_pos (And.intro hi1 hi2)]
  show next c (traj c π d t) (orderAt c π d t) (d t) ⟨i - 1, _⟩ = _
  simp only [next, outdatedAt, level]
  have : i - 1 + 2 = i + 1 := by omega
  rw [this]; rfl

theorem iter (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t n : ℕ)
    (hn : n ≤ c.m + c.L) : ∀ k : ℕ, k + 1 ≤ n →
    levelAt c π d (t + k) (n - k) = levelAt c π d t n -
      ∑ i ∈ Finset.Ico t (t + k), (d i : ℝ) - ∑ i ∈ Finset.Ico t (t + k), outdatedAt c π d i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := step c π d (t + k) (n - (k + 1)) (by omega) (by omega)
    have e1 : n - (k + 1) + 1 = n - k := by omega
    rw [e1, h1] at h2
    rw [show t + (k + 1) = t + k + 1 by omega, h2, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    ring

end PB7Aux

open PerishBaseStock.Backlog in
theorem solution (c : Params) (hm : 1 ≤ c.m) (π : Policy c) (d : CappedBaseStock.DemandPath)
    (t : ℕ) :
    levelAt c π d (t + c.L) c.m =
      levelAt c π d t (c.m + c.L) - ∑ i ∈ Finset.Ico t (t + c.L), (d i : ℝ) -
        ∑ i ∈ Finset.Ico t (t + c.L), outdatedAt c π d i := by
  have h := PB7Aux.iter c π d t (c.m + c.L) le_rfl c.L (by omega)
  rwa [show c.m + c.L - c.L = c.m by omega] at h
