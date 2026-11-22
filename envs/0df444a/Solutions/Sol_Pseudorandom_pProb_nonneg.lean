-- Prove2me | solution 1 for Pseudorandom.pProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:47.839541+00:00
-- url     : https://prove2.me/submissions/11409396-6a28-47cf-a9a9-2fc83abad668

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (S : (ι → α) → Prop) : 0 ≤ pProb P S := by
  classical
  unfold pProb
  exact pE_nonneg hP fun ω => by split_ifs <;> norm_num
end Pseudorandom
