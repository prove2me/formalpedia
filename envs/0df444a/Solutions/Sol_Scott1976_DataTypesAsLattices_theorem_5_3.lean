-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:11.466079+00:00
-- url     : https://prove2.me/submissions/52e24465-7f56-4ed0-a565-6b03b0e9c920

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_arrowR_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_graph_ext
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_3_i


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha.2 hb.2, arrowR_app]
end Scott1976.DataTypesAsLattices
