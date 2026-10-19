-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_card_omitted_external
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/8dfab33d-345f-4a74-b5d2-097223d3a4bd

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {m : ℕ} (b : Fin m) :
    Fintype.card {j : Fin m // j ≠ b} = m - 1 := by
  classical
  simp
end PermanentFormulaLowerBound
