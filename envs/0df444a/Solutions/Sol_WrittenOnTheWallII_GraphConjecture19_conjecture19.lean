-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture19.conjecture19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:34.648036+00:00
-- url     : https://prove2.me/submissions/28c80595-a765-4e88-963d-f48cccda1387

module
public import Definitions.Def_OpenMath_WOWII96
public import Definitions.Def_OpenMath_WOWII19
public import Definitions.Def_OpenMath_Upstream
public import Theorems.Thm_OpenMath_WOWII19_conjecture19


set_option autoImplicit true
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture19
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture19
theorem _root_.solution (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  exact OpenMath.WOWII19.conjecture19 G h_conn
end WrittenOnTheWallII.GraphConjecture19
