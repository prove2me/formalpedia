-- Prove2me | solution 1 for SizeRamsey.Plan.rightCopy_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:06.102282+00:00
-- url     : https://prove2.me/submissions/b96d068c-51d0-44cf-a8f6-357accc92cc4

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution :
    Function.Injective rightCopy := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [rightCopy] at this
  omega
end SizeRamsey.Plan
