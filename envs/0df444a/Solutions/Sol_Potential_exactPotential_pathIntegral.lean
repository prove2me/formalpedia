-- Prove2me | solution 1 for Potential.exactPotential_pathIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:52.502906+00:00
-- url     : https://prove2.me/submissions/916603fe-a58e-4536-afe9-a4702e7b11ff

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_endpoint_nil
public import Theorems.Thm_Potential_endpoint_cons
public import Theorems.Thm_Potential_pathIntegral_nil
public import Theorems.Thm_Potential_pathIntegral_cons

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) (s : Profile A) (ms : List (Move A)) :
    pathIntegral u s ms = P (endpoint s ms) - P s := by
  induction ms generalizing s with
  | nil => simp [pathIntegral_nil, endpoint_nil]
  | cons m ms ih =>
    rw [pathIntegral_cons, endpoint_cons, ih]
    have := hp s m.1 m.2
    linarith
end Potential
