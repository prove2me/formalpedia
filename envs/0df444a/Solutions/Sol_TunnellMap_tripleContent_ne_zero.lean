-- Prove2me | solution 1 for TunnellMap.tripleContent_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:09.23372+00:00
-- url     : https://prove2.me/submissions/6e323bc1-c5a2-42ce-a7d9-77f076de9a8c

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_triplePolynomial_ne_zero

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    tripleContent v ≠ 0 := by
  intro hc
  apply triplePolynomial_ne_zero hv
  exact Polynomial.content_eq_zero_iff.mp hc
end TunnellMap
