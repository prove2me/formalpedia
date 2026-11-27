-- Prove2me | solution 1 for SizeRamsey.Plan.leftCopy_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:20.466431+00:00
-- url     : https://prove2.me/submissions/6ad570ba-9aca-48fa-84a6-368a5f21fd78

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution (i j : Fin 6) :
    F17.Adj (leftCopy i) (leftCopy j) ↔
      k33MinusEdge.Adj i j := by
  fin_cases i <;> fin_cases j <;> decide
end SizeRamsey.Plan
