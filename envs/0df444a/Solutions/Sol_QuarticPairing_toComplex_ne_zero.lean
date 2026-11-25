-- Prove2me | solution 1 for QuarticPairing.toComplex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:39.115844+00:00
-- url     : https://prove2.me/submissions/1b7b92af-7110-4b58-9ce5-274f86b04273

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {c : GaussianInt} (hc : c ≠ 0) : GaussianInt.toComplex c ≠ 0 := by
  rwa [Ne, map_eq_zero_iff _ GaussianInt.toComplex_injective]
end QuarticPairing
