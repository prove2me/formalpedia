-- Prove2me | solution 1 for SmallRatio.sawtooth_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:15:23.328277+00:00
-- url     : https://prove2.me/submissions/fc9fb3a4-b8f8-4e14-8fa2-220fbe164e89

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution : sawtooth 0 = 0 := by simp [sawtooth]
end SmallRatio
