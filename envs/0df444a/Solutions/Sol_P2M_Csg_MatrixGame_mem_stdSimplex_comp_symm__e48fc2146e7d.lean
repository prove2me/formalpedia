-- Prove2me | solution 1 for P2M_Csg_MatrixGame_mem_stdSimplex_comp_symm__e48fc2146e7d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:14.342153+00:00
-- url     : https://prove2.me/submissions/e5d2d4f1-7a37-48de-912d-040bfe861ce9

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
theorem _root_.solution (e : J' ≃ J) {y' : J' → ℝ} (hy' : y' ∈ stdSimplex ℝ J') :
    y' ∘ ⇑e.symm ∈ stdSimplex ℝ J := by
  obtain ⟨hnonneg, hsum⟩ := hy'
  exact ⟨fun j => hnonneg (e.symm j), (Equiv.sum_comp e.symm y').trans hsum⟩
end Csg.MatrixGame
