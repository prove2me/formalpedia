-- Prove2me | solution 1 for SizeRamsey.Plan.copies_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:15.22626+00:00
-- url     : https://prove2.me/submissions/42d8b83b-fa42-4513-8a8b-dde5047cdd42

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution (i j : Fin 6) :
    leftCopy i ≠ rightCopy j := by
  intro h
  have := congrArg Fin.val h
  dsimp [leftCopy, rightCopy] at this
  omega
end SizeRamsey.Plan
