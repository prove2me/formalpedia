-- Prove2me | solution 1 for P2M_Csg_MatrixGame_mem_stdSimplex_comp__eaf65fcbba18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:19.222901+00:00
-- url     : https://prove2.me/submissions/743632fa-4ad2-4e0a-8569-c094dab5edfe

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
omit [Nonempty J] [DecidableEq J] [Nonempty J'] [DecidableEq J']
namespace Csg.MatrixGame
theorem _root_.solution (e : J' ≃ J) {y : J → ℝ} (hy : y ∈ stdSimplex ℝ J) :
    y ∘ ⇑e ∈ stdSimplex ℝ J' := by
  obtain ⟨hnonneg, hsum⟩ := hy
  exact ⟨fun j' => hnonneg (e j'), (Equiv.sum_comp e y).trans hsum⟩
end Csg.MatrixGame
