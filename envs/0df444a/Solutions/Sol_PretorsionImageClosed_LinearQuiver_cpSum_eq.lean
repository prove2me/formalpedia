-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.cpSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:19:52.327886+00:00
-- url     : https://prove2.me/submissions/83d86440-03fc-4883-92ca-bac2b546f67f

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isDelta_cpSum
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpSum_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_IsDelta_unique


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
theorem _root_.solution {B : ℕ → Rq[X]} (hB : IsGandhiFirst B) (n : ℕ) : cpSum n = B (n + 1) := by
  induction n with
  | zero => rw [cpSum_zero, hB.1]
  | succ n ih =>
    have h := hB.2 (n + 2) (by omega)
    have hm : n + 2 - 1 = n + 1 := rfl
    rw [hm, ← ih] at h
    exact (isDelta_cpSum n).unique h
end PretorsionImageClosed.LinearQuiver
