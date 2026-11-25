-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.mem_choices_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:50:51.145432+00:00
-- url     : https://prove2.me/submissions/dc6b728d-15fa-44c5-8238-24c60b8d691b

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
theorem _root_.solution {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {c : Option (Fin (n + 1))} :
    c ∈ choices p Cont ↔ Allowed p Cont c := by
  cases c with
  | none => simp [choices, Allowed]
  | some e => simp [choices, Allowed]
end PretorsionImageClosed.LinearQuiver
