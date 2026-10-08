-- Prove2me | solution 1 for WorstCaseEq.Identical.opt_ge_max
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:04.548273+00:00
-- url     : https://prove2.me/submissions/203e56a3-b4e1-429f-828e-dca37e27f942

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model
open WorstCaseEq.Identical

/-- PDF p. 4: the social optimum is at least the traffic of every single agent and at least the average
load `∑_i w_i / m`. -/
theorem solution {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∀ i, w i ≤ opt m w) ∧ (∑ i, w i) / m ≤ opt m w := by
  classical
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hload (s : Fin n → Fin m) (j : Fin m) : load w s j ≤ makespan w s := by
    exact Finset.le_sup' (f := load w s) (Finset.mem_univ j)
  have htotal (s : Fin n → Fin m) : ∑ j, load w s j = ∑ i, w i := by
    simp only [load, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  constructor
  · intro i
    unfold opt
    apply Finset.le_inf'
    intro s hs
    apply le_trans (b := load w s (s i)) _ (hload s (s i))
    unfold load
    exact Finset.single_le_sum (fun k _ => hw k) (by simp)
  · unfold opt
    apply Finset.le_inf'
    intro s hs
    apply (div_le_iff₀ hmpos).mpr
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hload s j)
    rw [htotal] at hh
    simpa [mul_comm] using hh


#print axioms solution
