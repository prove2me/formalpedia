-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.decompose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:22.678923+00:00
-- url     : https://prove2.me/submissions/06e6ed94-68b0-4566-a6fd-a38b399897f0

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_cramer_identity
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
theorem _root_.solution (r : Triple) :
    linComb3 (F.coeff₁ r) (F.coeff₂ r) (coeffZ (p := p) r) F.e₁ F.e₂ F.z = r := by
  have h := cramer_identity r F.e₁ F.e₂ F.z
  rw [F.cross_eq, F.det_eq_one] at h
  simpa [coeff₁, coeff₂, coeffZ, vsmul] using h
end TunnellMap.OrthogonalFrame
