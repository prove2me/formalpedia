-- Prove2me | solution 1 for TunnellMap.cramer_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:58.176511+00:00
-- url     : https://prove2.me/submissions/163b54a5-3c17-4ad7-9bf4-8b80d7639de2

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
theorem _root_.solution (r e₁ e₂ z : Triple) :
    linComb3 (dot r (cross e₂ z)) (dot r (cross z e₁))
      (dot r (cross e₁ e₂)) e₁ e₂ z =
      vsmul (det3 e₁ e₂ z) r := by
  apply Triple.ext <;> simp [linComb3, vadd, vsmul, det3, dot, cross] <;> ring
end TunnellMap
