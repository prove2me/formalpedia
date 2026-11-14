-- Prove2me | solution 1 for ProbabilityTheory.jumpCount_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:27:14.884009+00:00
-- url     : https://prove2.me/submissions/63e4d3c7-f842-4c4f-ab8e-29796a222304

import Mathlib.Order.Monotone.Defs
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory Filter
theorem solution {T : ℕ → ℝ} (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    Monotone (jumpCount T) := by
  intro a b hab
  by_contra hcon
  push Not at hcon
  have h1 : T (jumpCount T b) ≤ a := (lt_jumpCount_iff hmono htop _ _).mp hcon
  exact absurd ((lt_jumpCount_iff hmono htop _ _).mpr (h1.trans hab)) (lt_irrefl _)
