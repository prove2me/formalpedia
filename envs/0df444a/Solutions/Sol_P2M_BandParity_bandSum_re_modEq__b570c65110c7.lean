-- Prove2me | solution 1 for P2M_BandParity_bandSum_re_modEq__b570c65110c7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:29.97406+00:00
-- url     : https://prove2.me/submissions/52aa5fa4-0b32-46c2-ae3c-75827da8bcb8

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_card_cls
public import Theorems.Thm_BandParity_sq_bijOn_one
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_parSign_eq
public import Theorems.Thm_BandParity_parSign_mul_self
public import Theorems.Thm_BandParity_sum_sign_mul_modEq
public import Theorems.Thm_P2M_BandParity_bandSum_re__97b3040ddadc
public import Theorems.Thm_P2M_BandParity_matching__4d040604aa82
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) :
    (bandSum χ).re ≡ Q p [ZMOD 4] := by
  have hc := card_cls hχ (z := 1) (Or.inl rfl)
  have hm := matching' (cls χ 1) (cls χ 1) _ (sq_bijOn_one hχ hp8) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  have hself := sum_sign_mul_modEq (cls χ 1) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  simp only [parSign_mul_self, sum_const, nsmul_eq_mul, mul_one] at hself
  rw [bandSum_re' hχ hp8, Q, ← hc]
  exact hm.trans hself.symm
end BandParity
