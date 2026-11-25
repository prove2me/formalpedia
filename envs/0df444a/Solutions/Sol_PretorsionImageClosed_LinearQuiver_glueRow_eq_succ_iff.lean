-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.glueRow_eq_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:42:55.514251+00:00
-- url     : https://prove2.me/submissions/cb84f890-2d8d-4f9f-a511-f1ba20fb09e8

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
theorem _root_.solution {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    (glueRow p Cont).β a = n + 1 ↔ a ∈ Cont := by
  by_cases h : a ∈ Cont
  · rw [glueRow_apply_of_mem h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [glueRow_apply_of_notMem h]
    have := βext_le p a
    exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h⟩
end PretorsionImageClosed.LinearQuiver
