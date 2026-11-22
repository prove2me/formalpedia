-- Prove2me | solution 1 for Pseudorandom.pProb_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:26.651894+00:00
-- url     : https://prove2.me/submissions/e0854d50-f579-4841-9b7f-54a318522493

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution {S T : (ι → α) → Prop} (h : ∀ ω, S ω ↔ T ω) : pProb P S = pProb P T := by
  have : S = T := funext fun ω => propext (h ω)
  rw [this]
end Pseudorandom
