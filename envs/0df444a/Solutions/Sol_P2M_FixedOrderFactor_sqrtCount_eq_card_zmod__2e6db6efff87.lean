-- Prove2me | solution 1 for P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:51.319823+00:00
-- url     : https://prove2.me/submissions/2b073cc4-659f-485a-bea7-94b33288adf4

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_FixedOrderFactor_castHom_natCast_eq_neg_one_iff

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    sqrtCount M a s = (univ.filter fun y : ZMod M =>
      IsUnit y ∧ y ^ 2 = a ∧ ZMod.castHom hs (ZMod s) y = -1).card := by
  unfold sqrtCount
  refine card_nbij' (fun x => (x : ZMod M)) (fun y => y.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨(ZMod.isUnit_iff_coprime x M).2 hx.2.1, ?_, (castHom_natCast_eq_neg_one_iff hs x).2 hx.2.2.2⟩
    rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff']
    exact hx.2.2.1
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    have hy' : ((y.val : ℕ) : ZMod M) = y := ZMod.natCast_zmod_val y
    refine ⟨ZMod.val_lt y, (ZMod.isUnit_iff_coprime _ M).1 (by rw [hy']; exact hy.1), ?_,
      (castHom_natCast_eq_neg_one_iff hs _).1 (by rw [hy']; exact hy.2.2)⟩
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hy', hy.2.1]
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx
    exact ZMod.val_natCast_of_lt hx.1
  · intro y _
    exact ZMod.natCast_zmod_val y
end FixedOrderFactor
