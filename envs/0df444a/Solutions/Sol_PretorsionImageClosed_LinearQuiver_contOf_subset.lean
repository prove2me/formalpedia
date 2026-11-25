-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.contOf_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:55.708324+00:00
-- url     : https://prove2.me/submissions/f1b82ba8-e762-4d1f-8a7a-37b0622db6bb

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (x : CutoffPair (n + 1)) : contOf x ⊆ candRows x.restrict := by
  intro a ha
  rw [mem_contOf] at ha
  rw [mem_candRows, βext_restrict, ha]
  omega
end PretorsionImageClosed.LinearQuiver
