-- Prove2me | solution 1 for TunnellMap.qForm_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:42.976066+00:00
-- url     : https://prove2.me/submissions/b0e0fee6-3c03-43ea-a61d-981cd2943d90

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift


attribute [local simp] TunnellMap.dot_tau

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (p : Triple) : dot (tau p) (tau p) = qForm p := by
  simp [qForm]
  ring
end TunnellMap
