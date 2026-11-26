-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.gram_cubic_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:11.370707+00:00
-- url     : https://prove2.me/submissions/365cdfe6-8542-45ef-900c-6820155a65c2

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_gram_cubic_identity_general
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
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let γ := dot F.e₂ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    α * γ * ζ + 2 * β * δ * ε - α * ε ^ 2 - γ * δ ^ 2 - β ^ 2 * ζ = 1 := by
  dsimp
  rw [gram_cubic_identity_general, F.det_eq_one]
  norm_num
end TunnellMap.OrthogonalFrame
