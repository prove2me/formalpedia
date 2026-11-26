-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.affineQuadratic_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:44.141194+00:00
-- url     : https://prove2.me/submissions/360d3979-28a6-4509-b462-84e69ff90eed

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
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
theorem _root_.solution (A q b : ℤ) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let γ := dot F.e₂ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    let t := q * A
    quadraticHalfDiscriminant α (β * b + t * δ)
      (γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A) =
        F.halfDiscriminant A q b := by
  simp [quadraticHalfDiscriminant, halfDiscriminant]
end TunnellMap.OrthogonalFrame
