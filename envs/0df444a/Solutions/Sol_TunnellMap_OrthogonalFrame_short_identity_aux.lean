-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.short_identity_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:03.291074+00:00
-- url     : https://prove2.me/submissions/0bce31a9-92a8-4ae9-a57d-b3b3557f5912

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_det
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_cubic_identity
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
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    let n := dot p p
    let K := β * δ - α * ε
    K ^ 2 + n * (δ ^ 2 - α * ζ) = -α := by
  dsimp
  have hg := F.gram_det
  have hc := F.gram_cubic_identity
  dsimp at hc
  calc
    (dot F.e₁ F.e₂ * dot F.z F.e₁ - dot F.e₁ F.e₁ * dot F.z F.e₂) ^ 2 +
        dot p p * (dot F.z F.e₁ ^ 2 - dot F.e₁ F.e₁ * dot F.z F.z) =
      (dot F.e₁ F.e₂ * dot F.z F.e₁ - dot F.e₁ F.e₁ * dot F.z F.e₂) ^ 2 +
        (dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2) *
          (dot F.z F.e₁ ^ 2 - dot F.e₁ F.e₁ * dot F.z F.z) := by rw [hg]
    _ = -dot F.e₁ F.e₁ *
        (dot F.e₁ F.e₁ * dot F.e₂ F.e₂ * dot F.z F.z +
          2 * dot F.e₁ F.e₂ * dot F.z F.e₁ * dot F.z F.e₂ -
          dot F.e₁ F.e₁ * dot F.z F.e₂ ^ 2 -
          dot F.e₂ F.e₂ * dot F.z F.e₁ ^ 2 -
          dot F.e₁ F.e₂ ^ 2 * dot F.z F.z) := by ring
    _ = -dot F.e₁ F.e₁ := by rw [hc]; ring
end TunnellMap.OrthogonalFrame
