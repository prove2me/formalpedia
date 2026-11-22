-- Prove2me | solution 1 for Pseudorandom.IsPMF.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:13.612799+00:00
-- url     : https://prove2.me/submissions/ce748927-d04f-4876-a864-bf5455aba69f

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α]
namespace Pseudorandom
namespace IsPMF
theorem _root_.solution {n : ℕ} {P : Fin (n + 1) → α → ℝ} (hP : IsPMF P) :
    IsPMF (fun i : Fin n => P i.succ) :=
  ⟨fun _ a => hP.1 _ a, fun _ => hP.2 _⟩
end IsPMF
end Pseudorandom
