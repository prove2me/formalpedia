-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.halfDiscriminant_nonneg_iff_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:20.568172+00:00
-- url     : https://prove2.me/submissions/384289c7-45ff-42cb-a588-d129722025b8

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
import Definitions.Def_TunnellMap_ShortInterval
import Theorems.Thm_TunnellMap_square_le_iff_mem_floorCeilInterval
import Theorems.Thm_TunnellMap_OrthogonalFrame_short_interval_identity
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
theorem _root_.solution
    {n A q b : ℤ} (hn : 0 < n) (hpNorm : dot p p = n)
    (hAM :
      0 ≤ dot F.e₁ F.e₁ * (A * (n - q ^ 2 * A))) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let t := q * A
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    0 ≤ F.halfDiscriminant A q b ↔
      ⌈((t * K - Int.sqrt (α * M) : ℤ) : ℚ) / (n : ℚ)⌉ ≤ b ∧
        b ≤ ⌊((t * K + Int.sqrt (α * M) : ℤ) : ℚ) / (n : ℚ)⌋ := by
  dsimp
  have hid := F.short_interval_identity A q b
  rw [hpNorm] at hid
  dsimp at hid
  have hsign :
      0 ≤ F.halfDiscriminant A q b ↔
        (n * b - q * A *
          (dot F.e₁ F.e₂ * dot F.z F.e₁ -
            dot F.e₁ F.e₁ * dot F.z F.e₂)) ^ 2 ≤
          dot F.e₁ F.e₁ * (A * (n - q ^ 2 * A)) := by
    constructor <;> intro h <;> nlinarith
  exact hsign.trans (square_le_iff_mem_floorCeilInterval hn hAM)
end TunnellMap.OrthogonalFrame
