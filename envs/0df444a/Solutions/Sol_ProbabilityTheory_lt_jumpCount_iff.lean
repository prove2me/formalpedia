-- Prove2me | solution 1 for ProbabilityTheory.lt_jumpCount_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:17:26.886754+00:00
-- url     : https://prove2.me/submissions/e77d6bdf-1fdc-405c-b8ed-ed1738b7aac2

import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory Filter
theorem solution {T : ℕ → ℝ} (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (n : ℕ) (t : ℝ) :
    n < jumpCount T t ↔ T n ≤ t := by
  have hne : {m | t < T m}.Nonempty := (htop.eventually_gt_atTop t).exists
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hle : jumpCount T t ≤ n := Nat.sInf_le (show n ∈ {m | t < T m} from hcon)
    omega
  · intro h
    by_contra hcon
    push Not at hcon
    have hmem : t < T (jumpCount T t) := Nat.sInf_mem hne
    have : T (jumpCount T t) ≤ T n := hmono.monotone hcon
    linarith
