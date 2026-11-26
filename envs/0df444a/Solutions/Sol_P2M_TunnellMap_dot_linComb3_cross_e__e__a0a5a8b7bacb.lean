-- Prove2me | solution 1 for P2M_TunnellMap_dot_linComb3_cross_e__e__a0a5a8b7bacb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:04.269052+00:00
-- url     : https://prove2.me/submissions/b0376970-63a0-4c54-9421-c3c3f3ef13d8

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
theorem _root_.solution (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross e₁ e₂) = c * det3 e₁ e₂ z := by
  simp [linComb3, vadd, vsmul, det3, dot, cross]
  ring
end TunnellMap
