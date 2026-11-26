-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.short_interval_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:47.476627+00:00
-- url     : https://prove2.me/submissions/0191d9f7-ce40-455a-8f66-dab41e0bb80d

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
import Definitions.Def_TunnellMap_ShortInterval
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_cubic_identity
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_det
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
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let n := dot p p
    let t := q * A
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    n * F.halfDiscriminant A q b = α * M - (n * b - t * K) ^ 2 := by
  dsimp [halfDiscriminant]
  have hg := F.gram_det
  have hc := F.gram_cubic_identity
  dsimp at hc
  rw [← hg]
  linear_combination
    (-dot F.e₁ F.e₁ * q ^ 2 * A ^ 2) * hc
end TunnellMap.OrthogonalFrame
