-- Prove2me | solution 1 for P2M_FixedOrderFactor_sqrtCount_top_dichotomy__7a2906f2d2a7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:14.817922+00:00
-- url     : https://prove2.me/submissions/1a95c04f-4fc9-432f-958d-75a467ac0429

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = if ∃ h : ZMod M, IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1
      then sqrtCount M 1 r else 0 := by
  rw [sqrtCount_top' hr, sqrtCount_top' hr]
  split_ifs with hex
  · obtain ⟨h0, hu, hsq, hH⟩ := hex
    set u := hu.unit
    have hu0 : (u : ZMod M) = h0 := hu.unit_spec
    have hinvH : ZMod.castHom hr (ZMod r) ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      have h1 : ZMod.castHom hr (ZMod r) ((u⁻¹ : (ZMod M)ˣ) : ZMod M) *
          ZMod.castHom hr (ZMod r) (u : ZMod M) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rwa [hu0, hH, mul_one] at h1
    have hinvsq : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) ^ 2 * (a : ZMod M) = 1 := by
      rw [← hsq, ← hu0, ← mul_pow, Units.inv_mul, one_pow]
    refine card_nbij' (fun y => y * (u⁻¹ : (ZMod M)ˣ)) (fun y => y * u) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨hy.1.mul (Units.isUnit _), ?_, ?_⟩
      · rw [mul_pow, hy.2.1, mul_comm, hinvsq, Nat.cast_one]
      · rw [map_mul, hy.2.2, hinvH, mul_one]
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨hy.1.mul (Units.isUnit _), ?_, ?_⟩
      · rw [mul_pow, hy.2.1, Nat.cast_one, one_mul, hu0, hsq]
      · rw [map_mul, hy.2.2, hu0, hH, mul_one]
    · intro y _
      simp only [mul_assoc, Units.inv_mul, mul_one]
    · intro y _
      simp only [mul_assoc, Units.mul_inv, mul_one]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro y _ hy
    exact hex ⟨y, hy⟩
end FixedOrderFactor
