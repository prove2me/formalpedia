-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_orbitAvg_square__272802dadd0c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:17.185372+00:00
-- url     : https://prove2.me/submissions/3ebb2f36-d3cb-40fe-8cf5-0e5fc9e01a73

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    ∑ y ∈ univ.filter (fun y : ZMod M => IsUnit y ∧ y ^ 2 = a),
      ∑ t ∈ range s, orbitAvg s (((ZMod.castHom hs (ZMod s) y).val + 1) * t) =
      s * sqrtCount M a s := by
  have hs0 : 0 < s := Nat.pos_of_dvd_of_pos hs (Nat.pos_of_ne_zero (NeZero.ne M))
  have : NeZero s := ⟨hs0.ne'⟩
  simp_rw [sum_orbitAvg_mul' hs0]
  have hiff : ∀ y : ZMod M, s ∣ (ZMod.castHom hs (ZMod s) y).val + 1 ↔
      ZMod.castHom hs (ZMod s) y = -1 := by
    intro y
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val,
      eq_neg_iff_add_eq_zero]
  simp_rw [hiff]
  rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter, mul_comm, sqrtCount_eq_card_zmod' hs]
  simp only [and_assoc]
end FixedOrderFactor
