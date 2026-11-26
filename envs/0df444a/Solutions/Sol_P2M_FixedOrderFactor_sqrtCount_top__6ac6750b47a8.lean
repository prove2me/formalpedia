-- Prove2me | solution 1 for P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:54.60857+00:00
-- url     : https://prove2.me/submissions/b16500e4-6e90-498e-8354-ec5ef6049638

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = (univ.filter fun h : ZMod M =>
      IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1).card := by
  rw [sqrtCount_eq_card_zmod' hr]
  refine card_nbij' (fun y => -y) (fun y => -y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    refine ⟨hy.1.neg, by rw [neg_sq]; exact hy.2.1, ?_⟩
    rw [map_neg, hy.2.2, neg_neg]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    refine ⟨hy.1.neg, by rw [neg_sq]; exact hy.2.1, ?_⟩
    rw [map_neg, hy.2.2]
  · intro y _; exact neg_neg y
  · intro y _; exact neg_neg y
end FixedOrderFactor
