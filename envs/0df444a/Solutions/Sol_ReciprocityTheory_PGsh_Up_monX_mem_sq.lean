-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monX_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:24.130427+00:00
-- url     : https://prove2.me/submissions/c719af17-3a9e-4243-b950-7f6fd3d82604

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_mem_aug
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_split
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


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
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (D : Lifts H U X) {α : Nb p g} (h0 : α ≠ 0) (h1 : ∀ k, α ≠ Pi.single k 1) :
    monX D α ∈ sqIdeal (augIdeal H.AA.carrier) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h0
  have hj' : α j ≠ 0 := hj
  have hβ : Function.update α j (α j - 1) ≠ 0 := by
    intro hz
    apply h1 j
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same]
      simpa [Function.update_apply, sub_eq_zero] using congrFun hz i
    · rw [Pi.single_eq_of_ne hi]
      simpa [Function.update_apply, hi] using congrFun hz i
  exact Submodule.subset_span ⟨xL D j, D.x_mem j, monX D (Function.update α j (α j - 1)),
    monX_mem_aug D hβ, monX_split D hj'⟩
end ReciprocityTheory.PGsh.Up
