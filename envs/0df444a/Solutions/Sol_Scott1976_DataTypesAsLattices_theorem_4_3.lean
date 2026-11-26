-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:41.291971+00:00
-- url     : https://prove2.me/submissions/649b5037-225a-481d-93b5-c0bd3f31b1d6

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_ext
import Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_3_i

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (arrowR a b) := by
  change arrowR a b =
    graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha hb, arrowR_app]
end Scott1976.DataTypesAsLattices
