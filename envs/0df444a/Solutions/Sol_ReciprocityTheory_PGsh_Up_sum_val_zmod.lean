-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sum_val_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:47.010806+00:00
-- url     : https://prove2.me/submissions/c6609886-8ea8-4411-bb58-663cab21b246

import Definitions.Def_ReciprocityTheory_DualLattices_MonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (p : ℕ) [Fact p.Prime] : ∑ a : ZMod p, a.val = p * (p - 1) / 2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : Set.InjOn (fun a : ZMod p => a.val) (univ : Finset (ZMod p)) :=
    fun a _ b _ h => ZMod.val_injective p h
  have himg : (univ : Finset (ZMod p)).image (fun a => a.val) = range p := by
    ext i
    simp only [mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ZMod.val_lt a
    · intro hi
      exact ⟨(i : ZMod p), ZMod.val_cast_of_lt hi⟩
  rw [← Finset.sum_range_id, ← himg]
  exact (Finset.sum_image (f := fun i : ℕ => i) hinj).symm
end ReciprocityTheory.PGsh.Up
