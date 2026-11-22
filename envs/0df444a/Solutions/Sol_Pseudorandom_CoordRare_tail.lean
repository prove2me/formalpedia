-- Prove2me | solution 1 for Pseudorandom.CoordRare.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:52.047121+00:00
-- url     : https://prove2.me/submissions/8d30ff4f-00f0-448e-ae07-4abcc6e39f5b

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
namespace CoordRare
theorem _root_.solution {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {R : Fin (n + 1) → Finset α}
    (h : CoordRare f R) (b : α) :
    CoordRare (fun ω => f (Fin.cons b ω)) (fun i => R i.succ) := by
  intro i ω a a' ha ha'
  have := h i.succ (Fin.cons b ω) a a' ha ha'
  simpa [← Fin.cons_update] using this
end CoordRare
end Pseudorandom
