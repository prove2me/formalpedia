-- Prove2me | solution 1 for RamseyGraphs.ramsey_three_three_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:02.490112+00:00
-- url     : https://prove2.me/submissions/21982cb8-93b4-4073-bb30-76a43c2f20e4

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_ramsey_three_three_lower


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs
namespace RamseyGraphs
theorem _root_.solution :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 :=
  RamseyLib.ramsey_three_three_lower
end RamseyGraphs
