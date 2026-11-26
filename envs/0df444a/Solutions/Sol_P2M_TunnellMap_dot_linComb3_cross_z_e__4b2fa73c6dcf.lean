-- Prove2me | solution 1 for P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:03.063785+00:00
-- url     : https://prove2.me/submissions/499870e6-8dae-4574-87a9-627aaae5a69e

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
    dot (linComb3 a b c e₁ e₂ z) (cross z e₁) = b * det3 e₁ e₂ z := by
  simp [linComb3, vadd, vsmul, det3, dot, cross]
  ring
end TunnellMap
