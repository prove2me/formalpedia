-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture96.conjecture96
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:10.4387+00:00
-- url     : https://prove2.me/submissions/7896df94-edc7-4fb0-a44d-9df06a805b24

module
public import Definitions.Def_OpenMath_WOWII96
public import Definitions.Def_OpenMath_WOWII19
public import Definitions.Def_OpenMath_Upstream
public import Theorems.Thm_OpenMath_WOWII96_conjecture96


set_option autoImplicit true
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture96
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
namespace WrittenOnTheWallII.GraphConjecture96
theorem _root_.solution (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  exact OpenMath.WOWII96.conjecture96 G h
end WrittenOnTheWallII.GraphConjecture96
