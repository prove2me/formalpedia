-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.involutionPerm_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:23.043505+00:00
-- url     : https://prove2.me/submissions/a2797da8-553d-4d50-9504-f5aa1d75a9f0

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_involutionPerm_apply
import Theorems.Thm_ReciprocityTheory_PGsh_Up_involutionPerm_apply_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) : σ (e k) = e (pi2 e π hσ k) := by
  by_cases hk : e k = 0
  · rw [involutionPerm_apply_zero e π hσ k hk, hk, map_zero]
  · rw [involutionPerm_apply e π hσ k hk]
    exact hσ k
end ReciprocityTheory.PGsh.Up
