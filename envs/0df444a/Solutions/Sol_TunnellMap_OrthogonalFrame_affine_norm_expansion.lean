-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.affine_norm_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:46.723008+00:00
-- url     : https://prove2.me/submissions/0a590054-db62-4afd-9f0b-b9ab0b277b62

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
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution (t a b : ℤ) :
    dot (linComb3 a b t F.e₁ F.e₂ F.z)
      (linComb3 a b t F.e₁ F.e₂ F.z) =
      dot F.e₁ F.e₁ * a ^ 2 +
      2 * (dot F.e₁ F.e₂ * b + t * dot F.z F.e₁) * a +
      dot F.e₂ F.e₂ * b ^ 2 +
      2 * t * dot F.z F.e₂ * b + t ^ 2 * dot F.z F.z := by
  simp [linComb3, vadd, vsmul, dot]
  ring
end TunnellMap.OrthogonalFrame
