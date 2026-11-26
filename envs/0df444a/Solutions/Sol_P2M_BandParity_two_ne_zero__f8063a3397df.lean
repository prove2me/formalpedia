-- Prove2me | solution 1 for P2M_BandParity_two_ne_zero__f8063a3397df
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:52.018431+00:00
-- url     : https://prove2.me/submissions/eeb7e27a-ee49-46b3-944a-832b80296081

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_val_two

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h; have := val_two (p := p) hp2; rw [h, ZMod.val_zero] at this; omega
end BandParity
