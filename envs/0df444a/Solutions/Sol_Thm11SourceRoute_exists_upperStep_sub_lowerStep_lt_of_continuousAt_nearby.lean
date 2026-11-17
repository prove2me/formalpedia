-- Prove2me | solution 1 for Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:24:26.493211+00:00
-- url     : https://prove2.me/submissions/6c45bc34-24a9-44d0-ac32-1b56e371d7e2

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F002
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
import Theorems.Thm_Thm11SourceRoute_continuousAt_local_oscillation
import Theorems.Thm_Thm11SourceRoute_upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute
end Thm11SourceRoute
section Thm11SourceRoute
open Thm11SourceRoute


theorem solution
    {f : ℝ → ℝ} {a b c eps : ℝ}
    (hf : ContinuousAt f c)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : Partition a b) (i : Fin P.n),
        |P.pts i.castSucc - c| < delta →
        |P.pts i.succ - c| < delta →
          upperStep P f i - lowerStep P f i < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases continuousAt_local_oscillation hf hhalf with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P i hleft hright
  have hle :
      upperStep P f i - lowerStep P f i ≤ eps / 2 := by
    refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P i hAbove hBelow ?_
    intro x hx y hy
    exact le_of_lt (Hdelta x y
      (abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt P hx hleft hright)
      (abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt P hy hleft hright))
  linarith
end Thm11SourceRoute
