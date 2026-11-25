-- Prove2me | solution 1 for P2M_GlobalTheory_ExistsNatMulIsIntegral__main_38cfb947c5e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:41:48.46974+00:00
-- url     : https://prove2.me/submissions/0afb9a0e-43c8-4118-b00f-67ae5b581c41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNatMulIsIntegral
import Theorems.Thm_P2M_GlobalTheory_ExistsNatMulIsIntegral__exists_nat_mul_isIntegral_373366b61ebd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExistsNatMulIsIntegral₂
open NumberField
namespace GlobalTheory.ExistsNatMulIsIntegral₂
theorem _root_.solution : ∀ {E W : Type} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W] [inst_3 : Module E W]
    [inst_4 : Module (NumberField.RingOfIntegers E) W] [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W),
    ∀ x ∈ Submodule.span E (↑L : Set W), ∃ (k : ℕ), (0 : ℕ) < k ∧ k • x ∈ L := by
  intro E W _ _ _ _ _ _ L x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_pos, by simpa using h⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨k, hk, hkx⟩ := hx
    obtain ⟨d, hd, hdc⟩ := exists_nat_mul_isIntegral c
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let a : 𝓞 E := ⟨(d : E) * c, hdc⟩
    have ha : (algebraMap (𝓞 E) E a) = (d : E) * c := rfl
    have key : (d * k) • (c • x) = a • (k • x) := by
      rw [← algebraMap_smul E a (k • x), ha, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm c k x]
    rw [key]
    exact L.smul_mem a hkx
end GlobalTheory.ExistsNatMulIsIntegral₂
