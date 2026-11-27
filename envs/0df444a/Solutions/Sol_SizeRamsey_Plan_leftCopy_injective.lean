-- Prove2me | solution 1 for SizeRamsey.Plan.leftCopy_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:46.834169+00:00
-- url     : https://prove2.me/submissions/a0952a0a-0bbe-48a8-bcf6-fe6d43a82161

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution :
    Function.Injective leftCopy := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 12 => x.val) h
end SizeRamsey.Plan
