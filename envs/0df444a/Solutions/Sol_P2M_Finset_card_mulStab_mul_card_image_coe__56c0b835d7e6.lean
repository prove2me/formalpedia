-- Prove2me | solution 1 for P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:37.16442+00:00
-- url     : https://prove2.me/submissions/c7b6e90d-e342-46b8-ac23-3d534e6ed9d0

module
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Theorems.Thm_Finset_card_mulStab_dvd_card_mulStab

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
open Finset
variable {ι α : Type*}
local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s
variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}
namespace Finset
theorem _root_.solution (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #(s +ₛ stabilizer α (t : Set α)) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ (s +ˢ stabilizer α (t : Set α))
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp
end Finset
