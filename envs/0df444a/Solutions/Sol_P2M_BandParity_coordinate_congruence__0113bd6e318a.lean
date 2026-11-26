-- Prove2me | solution 1 for P2M_BandParity_coordinate_congruence__0113bd6e318a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:17:04.937842+00:00
-- url     : https://prove2.me/submissions/28b5c935-60f4-4027-9891-729dafca8776

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb
public import Theorems.Thm_P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914

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
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] :=
  (bandSum_im_modEq' hχ hp8 hpin).symm.trans (bandSum_im_modEq_coords' hχ hp8 hp5 hpin)
end BandParity
