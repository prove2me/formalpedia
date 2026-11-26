-- Prove2me | solution 1 for P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:20.969293+00:00
-- url     : https://prove2.me/submissions/f49c65eb-3fca-415c-a675-ca15dee0b154

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_card_cls
public import Theorems.Thm_BandParity_sq_bijOn_gi
public import Theorems.Thm_P2M_BandParity_coset_parities__d4e4b7d3cf9e
public import Theorems.Thm_BandParity_odd_Q
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_parSign_eq
public import Theorems.Thm_BandParity_parSign_neg
public import Theorems.Thm_BandParity_quartic_apply_neg_one
public import Theorems.Thm_BandParity_sum_cls_neg
public import Theorems.Thm_P2M_BandParity_bandSum_im__7ed5aaa03d73
public import Theorems.Thm_P2M_BandParity_matching__4d040604aa82
public import Theorems.Thm_P2M_BandParity_odd_t__8898b1b7a17c
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
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  have hc := card_cls hχ (z := gi) (by simp)
  have hm := matching' (cls χ gi) (cls χ (-1)) _ (sq_bijOn_gi hχ hp8) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  rw [sum_cls_neg hodd parSign (fun x hx => parSign_neg hp2 hx) one_ne_zero] at hm
  obtain ⟨h1, h2⟩ := coset_parities' hχ hp8 hp5 hpin
  rw [h1, h2, hc] at hm
  rw [bandSum_im' hχ hp8]
  refine hm.trans ?_
  obtain ⟨a, ha⟩ := odd_Q (p := p) hp8
  obtain ⟨b, hb⟩ := odd_t' hχ hp8 hp5
  have hQ : (((p - 1) / 4 : ℕ) : ℤ) = Q p := rfl
  rw [hQ]
  exact Int.modEq_iff_dvd.2 ⟨a + b + 1 + k χ, by rw [ha, hb]; ring⟩
end BandParity
