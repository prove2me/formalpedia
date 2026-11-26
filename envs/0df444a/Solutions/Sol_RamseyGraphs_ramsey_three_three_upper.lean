-- Prove2me | solution 1 for RamseyGraphs.ramsey_three_three_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:42.283287+00:00
-- url     : https://prove2.me/submissions/f887d4bb-dc30-4fa6-9818-67eeb6522210

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_ramsey_three_three_upper


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs
namespace RamseyGraphs
theorem _root_.solution (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 :=
  RamseyLib.ramsey_three_three_upper G
end RamseyGraphs
