-- Prove2me | solution 1 for PermanentRollout.sourceBlockAlpha_eq_squareZeroCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/a487aded-b9a0-4102-84e4-84a21d14907c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_coeff_columnLinearFormProduct_eq_permanent
import Theorems.Thm_PermanentRollout_sourceBlockAlpha_eq_permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {r d : ℕ} (U : Matrix (Fin r) (Fin (r - d)) ℂ)
    (omitted : Finset (Fin r))
    (homitted : omitted.card = d) :
    sourceBlockAlpha r d U omitted =
      squareZeroCoefficient r
        ((Finset.univ : Finset (Fin r)) \ omitted)
        (Ideal.Quotient.mk (squareZeroIdeal r)
          (columnLinearFormProduct U)) := by
  symm
  rw [squareZeroCoefficient_mk,
    coeff_columnLinearFormProduct_eq_permanent U
      ((Finset.univ : Finset (Fin r)) \ omitted)
      (sourceComplementSquareFreeRowEquiv r d omitted homitted),
    sourceBlockAlpha_eq_permanent U omitted
      (sourceComplementRowEquiv r d omitted homitted)]
  rfl
end PermanentRollout
