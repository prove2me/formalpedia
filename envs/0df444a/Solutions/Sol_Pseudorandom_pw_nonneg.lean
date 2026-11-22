-- Prove2me | solution 1 for Pseudorandom.pw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:53.412708+00:00
-- url     : https://prove2.me/submissions/7d2ae665-8279-4a95-886a-bffe72a4c0a8

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
omit [DecidableEq ι]
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (ω : ι → α) : 0 ≤ pw P ω :=
  prod_nonneg fun i _ => hP.1 i (ω i)
end Pseudorandom
