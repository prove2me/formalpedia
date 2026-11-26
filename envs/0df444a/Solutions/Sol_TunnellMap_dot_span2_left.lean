-- Prove2me | solution 1 for TunnellMap.dot_span2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:04.524906+00:00
-- url     : https://prove2.me/submissions/edad3963-036c-4ec9-94ad-667048de2961

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
theorem _root_.solution (p : Triple) {u v : Triple} (hu : dot p u = 0)
    (hv : dot p v = 0) (a b : ℤ) : dot p (span2 a b u v) = 0 := by
  simp only [dot, span2_apply] at hu hv ⊢
  linear_combination a * hu + b * hv
end TunnellMap
