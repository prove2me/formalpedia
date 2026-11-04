-- Prove2me | solution 1 for PerishBaseStock.Backlog.ec_30
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:23:04.255997+00:00
-- url     : https://prove2.me/submissions/415a2815-1c65-46a0-b8fb-0035afe8965d

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
    max (levelAt c π d t (c.m + c.L) - ∑ i ∈ Finset.Ico t (t + c.m + c.L), (d i : ℝ)) 0 ≤
      ∑ i ∈ Finset.Ico t (t + c.m + c.L), outdatedAt c π d i := by
  have hnn : ∀ i, 0 ≤ outdatedAt c π d i := fun i => le_max_right _ _
  refine max_le ?_ (Finset.sum_nonneg fun i _ => hnn i)
  have h := PB7Aux.iter c π d t (c.m + c.L) le_rfl (c.m + c.L - 1) (by omega)
  rw [show c.m + c.L - (c.m + c.L - 1) = 1 by omega] at h
  have ho : levelAt c π d (t + (c.m + c.L - 1)) 1 - (d (t + (c.m + c.L - 1)) : ℝ) ≤
      outdatedAt c π d (t + (c.m + c.L - 1)) := le_max_left _ _
  have e : t + c.m + c.L = t + (c.m + c.L - 1) + 1 := by omega
  rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
  linarith
