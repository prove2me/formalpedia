-- Prove2me | solution 1 for TunnellMap.primitiveDirection_negTriple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:11.022351+00:00
-- url     : https://prove2.me/submissions/cb5f784a-cd0c-4daa-a7a8-f1ae83029835

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_ne_zero
import Theorems.Thm_TunnellMap_orientDirection_neg
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


attribute [local simp] TunnellMap.primitivePartTriple_negTriple

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (negTriple v) = primitiveDirection v := by
  rw [primitiveDirection, primitivePartTriple_negTriple hv]
  exact orientDirection_neg (primitivePartTriple_ne_zero hv)
end TunnellMap
