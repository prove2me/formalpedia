-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.involutionPerm_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:22.905375+00:00
-- url     : https://prove2.me/submissions/56a1535f-80a2-4bf7-aaf6-2bce19513aee

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
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hinv : ∀ a, σ (σ a) = a) (k : Fin m) :
    pi2 e π hσ (pi2 e π hσ k) = k := by
  by_cases hk : e k = 0
  · rw [involutionPerm_apply_zero e π hσ k hk, involutionPerm_apply_zero e π hσ k hk]
  · have h1 : e (π k) ≠ 0 := by
      intro h0
      apply hk
      have h := hσ k
      rw [h0] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    rw [involutionPerm_apply e π hσ k hk, involutionPerm_apply e π hσ (π k) h1]
    by_contra hne
    have h2 : e (π (π k)) = e k := by
      rw [← hσ, ← hσ, hinv]
    have h3 := horth (π (π k)) k
    rw [if_neg hne, h2, horth k k, if_pos rfl] at h3
    exact hk h3
end ReciprocityTheory.PGsh.Up
