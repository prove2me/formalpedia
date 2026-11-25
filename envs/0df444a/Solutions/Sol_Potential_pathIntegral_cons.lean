-- Prove2me | solution 1 for Potential.pathIntegral_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:56:01.305901+00:00
-- url     : https://prove2.me/submissions/b0399a38-3b12-47f3-b7c4-23dd2f8e2b1e

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
public import Theorems.Thm_Potential_pathIntegral_nil
section
@[expose] public section
namespace Potential
private lemma pathIntegral_foldl_add {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) (ms : List (Move A)) (c : ℝ) :
    (ms.foldl (fun p m => (p.1 + u m.1 (Function.update p.2 m.1 m.2) - u m.1 p.2,
      Function.update p.2 m.1 m.2)) (c, s)).1 = c + pathIntegral u s ms := by
  induction ms generalizing s c with
  | nil => simp only [List.foldl_nil, pathIntegral_nil, add_zero]
  | cons m ms ih =>
    simp only [pathIntegral, List.foldl_cons, zero_add] at ih ⊢
    rw [ih (Function.update s m.1 m.2)
      (c + u m.1 (Function.update s m.1 m.2) - u m.1 s),
      ih (Function.update s m.1 m.2)
        (u m.1 (Function.update s m.1 m.2) - u m.1 s)]
    ring
end Potential
namespace Potential
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
end Potential
end
end

set_option autoImplicit true
@[expose] public section
public section
open Potential
namespace Potential
theorem _root_.solution {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) (m : Move A) (ms : List (Move A)) :
    pathIntegral u s (m :: ms) = u m.1 (Function.update s m.1 m.2) - u m.1 s +
      pathIntegral u (Function.update s m.1 m.2) ms := by
  simp only [pathIntegral, List.foldl_cons, zero_add]
  exact pathIntegral_foldl_add u (Function.update s m.1 m.2) ms
    (u m.1 (Function.update s m.1 m.2) - u m.1 s)
end Potential
