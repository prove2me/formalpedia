-- Prove2me | solution 1 for P2M_BandParity_bandSum_im__7ed5aaa03d73
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:26.619819+00:00
-- url     : https://prove2.me/submissions/9dd9c6d0-b463-43f6-bc14-9591df8c664c

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_im_add_gi_mul
public import Theorems.Thm_BandParity_bandSum_eq

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
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) := by
  rw [bandSum_eq hχ hp8, im_add_gi_mul]
end BandParity
