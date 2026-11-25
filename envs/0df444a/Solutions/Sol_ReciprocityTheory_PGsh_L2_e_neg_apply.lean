-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.e_neg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:57:26.286906+00:00
-- url     : https://prove2.me/submissions/a38471ce-2967-47a3-9d97-a8bfe215b15a

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_e_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem addChar_apply_ne_zero_dual_lattices (ψ : AddChar N C) (a : N) : ψ a ≠ 0 := by
  intro h0
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h') (h : H) (a : N) :
    e (-h) a = e h (-a) := by
  have h1 := he (-h) h
  have hz : -h + h = 0 := by simp
  rw [hz, e_zero e he] at h1
  have h2 := congrArg (fun ψ : AddChar N C => ψ a) h1
  simp only [AddChar.mul_apply, AddChar.one_apply] at h2
  have h3 : e h (-a) * e h a = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  exact mul_right_cancel₀ (addChar_apply_ne_zero_dual_lattices (e h) a) (h2.symm.trans h3.symm)
end ReciprocityTheory.PGsh.L2
