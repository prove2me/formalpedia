-- Prove2me | solution 1 for Thm11SourceRoute.continuousAt_local_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:44:38.497299+00:00
-- url     : https://prove2.me/submissions/603af8b7-c81e-477a-90cb-7000f1836daa

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F001
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

section Thm11SourceRoute
open Thm11SourceRoute


theorem solution {f : ℝ → ℝ} {c eps : ℝ}
    (hf : ContinuousAt f c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x y : ℝ,
        |x - c| < delta → |y - c| < delta → |f x - f y| < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases continuousAt_abs_sub_lt hf hhalf with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x y hx hy
  have hx' := Hdelta x hx
  have hy' := Hdelta y hy
  have htri : |f x - f y| ≤ |f x - f c| + |f y - f c| := by
    calc
      |f x - f y| = |(f x - f c) + -(f y - f c)| := by ring_nf
      _ ≤ |f x - f c| + |-(f y - f c)| :=
        abs_add_le (f x - f c) (-(f y - f c))
      _ = |f x - f c| + |f y - f c| := by rw [abs_neg]
  linarith
end Thm11SourceRoute
