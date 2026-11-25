-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.lt_glueRow_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:15.509799+00:00
-- url     : https://prove2.me/submissions/88d78ea0-14e5-40b3-bf16-4ab2e48f81c3

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
    n < (glueRow p Cont).β a ↔ a ∈ Cont := by
  by_cases h : a ∈ Cont
  · rw [glueRow_apply_of_mem h]
    exact ⟨fun _ => h, fun _ => Nat.lt_succ_self _⟩
  · rw [glueRow_apply_of_notMem h]
    have := βext_le p a
    exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h⟩
end PretorsionImageClosed.LinearQuiver
