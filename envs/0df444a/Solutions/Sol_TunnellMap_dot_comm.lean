-- Prove2me | solution 1 for TunnellMap.dot_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:49.281804+00:00
-- url     : https://prove2.me/submissions/721ee823-2775-4e0f-afaf-79e3b980d54f

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (p q : Triple) : dot p q = dot q p := by
  simp [dot]
  ring
end TunnellMap
