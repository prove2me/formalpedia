-- Prove2me | solution 1 for PvsNP.mem_P_of_polyTimeReducible
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:32:23.824456+00:00
-- url     : https://prove2.me/submissions/6bf47917-742a-4cad-acb8-2a676ded9461

import Definitions.Def_PvsNP_reductions
import Theorems.Thm_PvsNP_isPolyTime_comp

open PvsNP

theorem solution (L K : DecisionProblem)
    (hLK : PolyTimeReducible L K) (hK : K ∈ P) : L ∈ P := by
  obtain ⟨f, hf, hfL⟩ := hLK
  have hcomp : IsPolyTime (K ∘ f) := isPolyTime_comp f K hf hK
  have hEq : L = K ∘ f := funext hfL
  rw [hEq]
  exact hcomp
