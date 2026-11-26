-- Prove2me | solution 1 for TunnellMap.cross_span2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:58.027039+00:00
-- url     : https://prove2.me/submissions/72c50918-16bb-43c2-ba8d-26bd6d2da2dd

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
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



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (a b c d : ℤ) (u v : Triple) :
    cross (span2 a b u v) (span2 c d u v) = vsmul (a * d - b * c) (cross u v) := by
  apply Triple.ext <;> simp [cross, span2, vadd, vsmul] <;> ring
end TunnellMap
