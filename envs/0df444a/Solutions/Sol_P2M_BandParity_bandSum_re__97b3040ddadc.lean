-- Prove2me | solution 1 for P2M_BandParity_bandSum_re__97b3040ddadc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:29.548072+00:00
-- url     : https://prove2.me/submissions/afe260d1-81c1-4693-bc26-7e55484976ba

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_re_add_gi_mul
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
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) := by
  rw [bandSum_eq hχ hp8, re_add_gi_mul]
end BandParity
