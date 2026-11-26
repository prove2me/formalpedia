-- Prove2me | solution 1 for TunnellMap.tripleContent_primitivePartTriple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:41.952493+00:00
-- url     : https://prove2.me/submissions/391aed64-af3c-4ea1-a10c-c80992388363

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_triplePolynomial_primitivePartTriple

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) :
    tripleContent (primitivePartTriple v) = 1 := by
  unfold tripleContent
  rw [triplePolynomial_primitivePartTriple]
  exact Polynomial.content_primPart _
end TunnellMap
