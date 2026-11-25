-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.colValue_colOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:50.32754+00:00
-- url     : https://prove2.me/submissions/6a0adca4-fc85-4a54-98c1-6f7ee15fc426

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
theorem _root_.solution (x : CutoffPair (n + 1)) : colValue (colOf x) = x.1.2.α (Fin.last n) := by
  unfold colOf
  split_ifs with h
  · simp [colValue, h]
  · simp only [colValue]
    omega
end PretorsionImageClosed.LinearQuiver
