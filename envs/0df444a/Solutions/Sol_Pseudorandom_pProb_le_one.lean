-- Prove2me | solution 1 for Pseudorandom.pProb_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:12.42505+00:00
-- url     : https://prove2.me/submissions/e94a34b4-e6df-495c-b8c4-62009c6df5d5

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_const
public import Theorems.Thm_Pseudorandom_pE_mono

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (S : (ι → α) → Prop) : pProb P S ≤ 1 := by
  classical
  unfold pProb
  calc _ ≤ pE P (fun _ => (1 : ℝ)) := pE_mono hP fun ω => by split_ifs <;> norm_num
    _ = 1 := pE_const hP 1
end Pseudorandom
