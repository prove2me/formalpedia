-- Prove2me | solution 1 for TunnellMap.primitiveDirection_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:32.22669+00:00
-- url     : https://prove2.me/submissions/aee49b3d-14c9-404c-8c51-193e9bbeebfa

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_primitivePartTriple_ne_zero
import Theorems.Thm_TunnellMap_orientDirection_firstNonzeroPositive
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau


attribute [local simp] TunnellMap.tripleContent_primitiveDirection

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (primitiveDirection v) = primitiveDirection v := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_primitiveDirection v
  · exact orientDirection_firstNonzeroPositive (primitivePartTriple_ne_zero hv)
end TunnellMap
