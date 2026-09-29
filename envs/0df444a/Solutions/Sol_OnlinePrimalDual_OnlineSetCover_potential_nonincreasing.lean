-- Prove2me | solution 1 for OnlinePrimalDual.OnlineSetCover.potential_nonincreasing
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:24:53.044371+00:00
-- url     : https://prove2.me/submissions/bf7c9685-ad96-47a8-baef-1b0df5d796b4

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

open OnlinePrimalDual.OnlineSetCover

/-- Counterexample: without the book's standing assumption `c_s ≤ α`, the expected potential can
increase.  Take two elements, a single set `s` containing no element, cost `c_s = 4`, `α = 1/2`,
`w = 0`, `w' s = δ = log(4/3)/(2 log 2)` (so `p = 1 - 2^{-2δ} = 1/4`) and `C = ∅`. -/
theorem solution : ¬ (∀ {E T : Type} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα_pos : 0 < α)
    (w w' : T → ℝ) (C : Finset T) (s : T)
    (hw'_off : ∀ t, t ≠ s → w' t = w t) (hw'_ge : w s ≤ w' s)
    (hE : 1 ≤ Fintype.card E),
    let n : ℝ := (Fintype.card E : ℝ)
    let p : ℝ := 1 - n ^ (-2 * (w' s - w s))
    p * potential inst w' (insert s C) α + (1 - p) * potential inst w' C α ≤
      potential inst w C α) := by
  intro H
  let inst : SetCoverInstance (Fin 2) Unit := ⟨fun _ => ∅, fun _ => 4, fun _ => by norm_num⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  set δ : ℝ := Real.log (4 / 3) / (2 * Real.log 2) with hδ
  have hδpos : 0 ≤ δ := div_nonneg hl43.le (by linarith)
  have h := H inst (1 / 2) (by norm_num) (fun _ => 0) (fun _ => δ) ∅ ()
    (fun t ht => absurd (Subsingleton.elim t ()) ht) (by simpa using hδpos) (by simp)
  have hcov : ∀ (C : Finset Unit) (e : Fin 2), ¬ coveredBy inst C e := by
    intro C e ⟨t, ht, _⟩
    simp [inst] at ht
  have hpot : ∀ (w : Unit → ℝ) (C : Finset Unit), potential inst w C (1 / 2) =
      2 + 2 * Real.exp (4 * (if () ∈ C then (1 : ℝ) else 0) - 3 * w () * 4 * Real.log 2) := by
    intro w C
    simp only [potential, elementWeight, hcov, not_false_eq_true, Finset.filter_true_of_mem,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    by_cases hC : () ∈ C
    · simp [inst, hC]
    · simp [inst, hC]
  have e1 : (2:ℝ) ^ (-2 * (δ - 0)) = 3 / 4 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have : Real.log 2 * (-2 * (δ - 0)) = -Real.log (4 / 3) := by
      rw [hδ, sub_zero]; field_simp [hl2.ne']
    rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have e2 : 12 * δ * Real.log 2 = 6 * Real.log (4 / 3) := by
    rw [hδ]; field_simp [hl2.ne']; ring
  have hlog : 6 * Real.log (4 / 3) < 2 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 4 / 3) (by norm_num)
    linarith
  have hX : 4 < Real.exp (4 - 12 * δ * Real.log 2) := by
    rw [e2]
    have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ 4 - 6 * Real.log (4 / 3))
    nlinarith
  have hY := Real.exp_pos (-(12 * δ * Real.log 2))
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  rw [hpot, hpot, hpot, e1] at h
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false, if_true, if_false] at h
  have ex1 : 4 * (1 : ℝ) - 3 * δ * 4 * Real.log 2 = 4 - 12 * δ * Real.log 2 := by ring
  have ex2 : 4 * (0 : ℝ) - 3 * δ * 4 * Real.log 2 = -(12 * δ * Real.log 2) := by ring
  have ex3 : 4 * (0 : ℝ) - 3 * 0 * 4 * Real.log 2 = 0 := by ring
  rw [ex1, ex2, ex3, Real.exp_zero] at h
  nlinarith
