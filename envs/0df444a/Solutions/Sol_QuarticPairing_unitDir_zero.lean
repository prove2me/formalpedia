-- Prove2me | solution 1 for QuarticPairing.unitDir_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:15.546809+00:00
-- url     : https://prove2.me/submissions/5e88d5b4-1d05-4d2c-b5fa-7d9656d49c38

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
theorem _root_.solution : unitDir 0 = 0 := by simp [unitDir]
end QuarticPairing
