-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.mem_model_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:52:55.064487+00:00
-- url     : https://prove2.me/submissions/d9f9f10e-c75f-419a-9e08-d8db1bc9c53a

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_mem_choices_iff

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
theorem _root_.solution {p : CutoffPair n} {y : Σ _ : Finset (Fin (n + 1)), Option (Fin (n + 1))} :
    y ∈ model p ↔ y.1 ⊆ candRows p ∧ Allowed p y.1 y.2 := by
  rw [model, Finset.mem_sigma, Finset.mem_powerset, mem_choices_iff]
end PretorsionImageClosed.LinearQuiver
