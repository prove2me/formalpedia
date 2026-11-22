-- Prove2me | solution 1 for Pseudorandom.CoordGap.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:43.993405+00:00
-- url     : https://prove2.me/submissions/c6876f66-555c-4959-883e-d8f42f46da83

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*}
namespace Pseudorandom
namespace CoordGap
theorem _root_.solution {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {c : Fin (n + 1) → ℝ}
    (h : CoordGap f c) (b : α) :
    CoordGap (fun ω => f (Fin.cons b ω)) (fun i => c i.succ) := by
  intro i ω a a'
  have := h i.succ (Fin.cons b ω) a a'
  simpa [← Fin.cons_update] using this
end CoordGap
end Pseudorandom
