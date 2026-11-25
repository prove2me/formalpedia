-- Prove2me | solution 1 for Potential.vertices_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:01:31.074272+00:00
-- url     : https://prove2.me/submissions/1d9bf6f2-4bdc-4ca4-9707-594c99e38386

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
section
@[expose] public section
namespace Potential
end Potential
namespace Potential
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
private lemma vertices_foldl_prefix (s : Profile A) (ms : List (Move A))
    (pre acc : List (Profile A)) :
    (ms.foldl (fun p m => (Function.update p.1 m.1 m.2,
      p.2 ++ [Function.update p.1 m.1 m.2])) (s, pre ++ acc)).2 =
      pre ++ (ms.foldl (fun p m => (Function.update p.1 m.1 m.2,
        p.2 ++ [Function.update p.1 m.1 m.2])) (s, acc)).2 := by
  induction ms generalizing s acc with
  | nil => rfl
  | cons m ms ih =>
    simpa only [List.foldl_cons, List.append_assoc] using
      ih (Function.update s m.1 m.2) (acc ++ [Function.update s m.1 m.2])
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
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (s : Profile A) (m : Move A) (ms : List (Move A)) :
    vertices s (m :: ms) = s :: vertices (Function.update s m.1 m.2) ms := by
  simpa only [vertices, List.foldl_cons, List.singleton_append] using
    vertices_foldl_prefix (Function.update s m.1 m.2) ms [s]
      [Function.update s m.1 m.2]
end Potential
