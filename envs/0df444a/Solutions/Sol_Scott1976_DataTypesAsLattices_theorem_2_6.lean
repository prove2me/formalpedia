-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:41.926047+00:00
-- url     : https://prove2.me/submissions/5d5469f2-ca49-4103-ab7c-95fc253e7516

import Mathlib.Computability.RE
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Computability

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    IsComputable f ↔ IsRE (graph f) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hf, h⟩
end Scott1976.DataTypesAsLattices
