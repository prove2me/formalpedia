-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.affine_norm_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:33.388236+00:00
-- url     : https://prove2.me/submissions/3a054bcd-a052-4b2c-a038-89c807d33326

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
import Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_expansion
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
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution (A q a b : ℤ) :
    dot (linComb3 a b (q * A) F.e₁ F.e₂ F.z)
        (linComb3 a b (q * A) F.e₁ F.e₂ F.z) = A ↔
      F.affineQuadratic A q a b = 0 := by
  rw [F.affine_norm_expansion]
  simp [affineQuadratic]
  constructor <;> intro h <;> linarith
end TunnellMap.OrthogonalFrame
