-- Prove2me | solution 1 for QuarterSumLadder.weight_two_integrality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:51.948569+00:00
-- url     : https://prove2.me/submissions/4e6026a7-8685-47b0-a5b2-43693de5164d

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_T2_eq
public import Theorems.Thm_QuarterSumLadder_p_dvd_U
public import Theorems.Thm_QuarterSumLadder_p_mul_c0
public import Theorems.Thm_QuarterSumLadder_p_mul_c1


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (∀ z : GaussianInt, (p : ℤ) ∣ U χ z) ∧ (p : ℤ) * c0 χ = U χ 1 - U χ (-1) ∧
      (p : ℤ) * c1 χ = U χ gi - U χ (-gi) ∧ T2 χ = (p : GaussianInt) * B2 χ :=
  ⟨fun _ => p_dvd_U hp8 hχ, p_mul_c0 hp8 hχ, p_mul_c1 hp8 hχ, T2_eq hp8 hχ⟩
end QuarterSumLadder
