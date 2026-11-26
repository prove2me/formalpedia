-- Prove2me | solution 1 for TunnellMap.gram_cubic_identity_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:12.911804+00:00
-- url     : https://prove2.me/submissions/f85710fa-df4d-4086-a907-7ebcc2ba820d

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift


attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.qForm_tau

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (e₁ e₂ z : Triple) :
    dot e₁ e₁ * dot e₂ e₂ * dot z z +
      2 * dot e₁ e₂ * dot z e₁ * dot z e₂ -
      dot e₁ e₁ * dot z e₂ ^ 2 -
      dot e₂ e₂ * dot z e₁ ^ 2 -
      dot e₁ e₂ ^ 2 * dot z z = det3 e₁ e₂ z ^ 2 := by
  simp [dot, det3, cross]
  ring
end TunnellMap
