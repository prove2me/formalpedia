-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.linComb3_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:58.260637+00:00
-- url     : https://prove2.me/submissions/949c4cc0-bb4c-4fdd-9931-e62ae7166608

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_e__z_b28283f150ec
import Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf
import Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_e__e__a0a5a8b7bacb
import Theorems.Thm_TunnellMap_OrthogonalFrame_det_eq_one
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
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution :
    Function.Injective (fun abc : ℤ × ℤ × ℤ =>
      linComb3 abc.1 abc.2.1 abc.2.2 F.e₁ F.e₂ F.z) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only at h
  have ha := congrArg (fun r => dot r (cross F.e₂ F.z)) h
  have hb := congrArg (fun r => dot r (cross F.z F.e₁)) h
  have hc := congrArg (fun r => dot r (cross F.e₁ F.e₂)) h
  simp only [dot_linComb3_cross_e₂_z, dot_linComb3_cross_z_e₁,
    dot_linComb3_cross_e₁_e₂, F.det_eq_one, mul_one] at ha hb hc
  subst ha; subst hb; subst hc; rfl
end TunnellMap.OrthogonalFrame
