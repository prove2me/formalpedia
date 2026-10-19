-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockCyclicRootFamily_pair_inner_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/857c5568-585b-46dc-b97b-6461f13627fc

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterBlockRootSubgroups_pair_inner_sq_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    {H : Type v₁} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule (ZMod 2) R) [Finite W]
    (π : UnitaryRepresentation
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) H)
    (i j : Fin 3) (hij : i ≠ j) (a b : H)
    (ha : a ∈ unitaryFixedSubmodule π
      (finiteOuterBlockCyclicRootFamily W i))
    (haQ : a ∈
      (unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W i) ⊓
       unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W j))ᗮ)
    (hb : b ∈ unitaryFixedSubmodule π
      (finiteOuterBlockCyclicRootFamily W j))
    (hbQ : b ∈
      (unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W i) ⊓
       unitaryFixedSubmodule π (finiteOuterBlockCyclicRootFamily W j))ᗮ) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact finiteOuterBlockRootSubgroups_pair_inner_sq_le
      W 0 1 2 (by decide) (by decide) (by decide)
      π ha hb haQ hbQ
  · rw [inf_comm] at haQ hbQ
    have h := finiteOuterBlockRootSubgroups_pair_inner_sq_le
        W 2 0 1 (by decide) (by decide) (by decide)
        π hb ha hbQ haQ
    calc
      8 * ‖inner ℂ a b‖ ^ 2 = 8 * ‖inner ℂ b a‖ ^ 2 := by
        rw [norm_inner_symm a b]
      _ ≤ ‖b‖ ^ 2 * ‖a‖ ^ 2 := h
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by rw [mul_comm]
  · rw [inf_comm] at haQ hbQ
    have h := finiteOuterBlockRootSubgroups_pair_inner_sq_le
        W 0 1 2 (by decide) (by decide) (by decide)
        π hb ha hbQ haQ
    calc
      8 * ‖inner ℂ a b‖ ^ 2 = 8 * ‖inner ℂ b a‖ ^ 2 := by
        rw [norm_inner_symm a b]
      _ ≤ ‖b‖ ^ 2 * ‖a‖ ^ 2 := h
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by rw [mul_comm]
  · exact (hij rfl).elim
  · exact finiteOuterBlockRootSubgroups_pair_inner_sq_le
      W 1 2 0 (by decide) (by decide) (by decide)
      π ha hb haQ hbQ
  · exact finiteOuterBlockRootSubgroups_pair_inner_sq_le
      W 2 0 1 (by decide) (by decide) (by decide)
      π ha hb haQ hbQ
  · rw [inf_comm] at haQ hbQ
    have h := finiteOuterBlockRootSubgroups_pair_inner_sq_le
        W 1 2 0 (by decide) (by decide) (by decide)
        π hb ha hbQ haQ
    calc
      8 * ‖inner ℂ a b‖ ^ 2 = 8 * ‖inner ℂ b a‖ ^ 2 := by
        rw [norm_inner_symm a b]
      _ ≤ ‖b‖ ^ 2 * ‖a‖ ^ 2 := h
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by rw [mul_comm]
  · exact (hij rfl).elim
end SoficGroups
