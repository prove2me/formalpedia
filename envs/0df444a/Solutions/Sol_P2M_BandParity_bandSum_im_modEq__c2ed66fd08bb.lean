-- Prove2me | solution 1 for P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:11.241232+00:00
-- url     : https://prove2.me/submissions/a2a81067-4af8-4a43-b2fa-8c6825502e82

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_sq_bijOn_gi
public import Theorems.Thm_BandParity_two_mul_bijOn_gi
public import Theorems.Thm_P2M_BandParity_lag_identity__1cd92334e44b
public import Theorems.Thm_BandParity_parSign_eq
public import Theorems.Thm_P2M_BandParity_bandSum_im__7ed5aaa03d73
public import Theorems.Thm_P2M_BandParity_matching_indep__280075205c52


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] := by
  rw [bandSum_im' hχ hp8, ← lag_identity' hχ hp8]
  exact matching_indep' (cls χ gi) (cls χ (-1)) _ _ (sq_bijOn_gi hχ hp8)
    (two_mul_bijOn_gi hχ hp8 hpin) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
end BandParity
