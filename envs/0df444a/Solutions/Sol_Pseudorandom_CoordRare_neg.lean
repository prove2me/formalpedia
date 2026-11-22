-- Prove2me | solution 1 for Pseudorandom.CoordRare.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:55.827546+00:00
-- url     : https://prove2.me/submissions/8f6328c4-8885-4e0b-a011-a4e42cc5d5cc

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
theorem _root_.solution {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {R : ι → Finset α}
    (h : CoordRare f R) : CoordRare (fun ω => -f ω) R := by
  intro i ω a b ha hb
  simp [h i ω a b ha hb]
end CoordRare
end Pseudorandom
