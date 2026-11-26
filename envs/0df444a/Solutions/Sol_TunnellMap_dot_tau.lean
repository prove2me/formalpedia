-- Prove2me | solution 1 for TunnellMap.dot_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:32.741746+00:00
-- url     : https://prove2.me/submissions/13779952-9427-48e5-b69a-fb5a7f64323a

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
theorem _root_.solution (p q : Triple) : dot (tau p) (tau q) =
    2 * p.x * q.x + p.y * q.y + 2 * p.z * q.z := by
  simp [dot, tau]
  ring
end TunnellMap
