-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.corollary_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:28:43.212622+00:00
-- url     : https://prove2.me/submissions/24bd0e5e-be08-4a3e-b286-650856cab8c7

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Theorems.Thm_ThinFlowSP_Breakpoints_theorem_14

open ThinFlowSP.Breakpoints in
theorem solution (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (x xh : G.A → ℝ) (l lh : G.V → ℝ) (val : ℝ)
    (hx : IsStaticFlow G x val) (hxh : IsStaticFlow G xh val)
    (hl : IsThinFlowLabels G Astar ν x l) (hlh : IsThinFlowLabels G Astar ν xh lh)
    (hs : l G.s = lh G.s) :
    l = lh := by
  funext v
  exact le_antisymm
    (theorem_14 G Astar ν hG hst hν x xh l lh val val hx hxh hl hlh le_rfl hs.le v)
    (theorem_14 G Astar ν hG hst hν xh x lh l val val hxh hx hlh hl le_rfl hs.ge v)
