-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Types.types8_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:05:45.015808+00:00
-- url     : https://prove2.me/submissions/c1333927-d926-4949-9a3b-8d58073720e9

import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22TypeSplit_filteredPrefix_eq_nil_of_budget
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22TypeSplit_filteredPrefix_three


namespace Sensitivity213981Formal
section
/- Split the exact active-type enumeration into small, independently checked
prefixes. This changes no enumeration predicate or final equality statement. -/


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

namespace ThreeBoundEndpoint22TypeSplit
open ThreeBoundQ3



theorem activeTypes_eq_filteredPrefix (n : ℕ) :
    ThreeBoundRelaxedCoverage.activeTypes n = filteredPrefix [] 0 n := by
  simp only [ThreeBoundRelaxedCoverage.activeTypes, filteredPrefix,
    List.nil_append, List.map_id']





end ThreeBoundEndpoint22TypeSplit




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Sound early rejection of a type-list pref. -/

set_option autoImplicit false
namespace ThreeBoundEndpoint22TypeSplit
open ThreeBoundQ3

theorem allowedTypes_append_left (xs ys : List Kind)
    (h : allowedTypes (xs ++ ys)) : allowedTypes xs := by
  constructor
  · intro k
    have hk : k.val <  (xs ++ ys).length + 1 := by
      simp only [List.length_append]
      omega
    have hb := h.1 ⟨k.val,hk⟩
    have hle : k.val ≤  xs.length := by omega
    simpa only [List.take_append_of_le_length hle] using hb
  · intro q
    have hp := h.2 q
    rw [List.filter_append,List.length_append] at hp
    omega

theorem filteredPrefix_eq_nil_of_not_allowed
    (pref : List Kind) (lo n : ℕ) (h : ¬ allowedTypes pref) :
    filteredPrefix pref lo n = [] := by
  unfold filteredPrefix
  apply List.filter_eq_nil_iff.mpr
  intro ts hts
  obtain ⟨suffix,hsuffix,rfl⟩ := List.mem_map.mp hts
  intro hallowed
  exact h (allowedTypes_append_left pref suffix (of_decide_eq_true hallowed))






end ThreeBoundEndpoint22TypeSplit




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Expand only the finite ordered prefix skeleton with an opaque function. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22TypeSplit
open ThreeBoundQ3

theorem ordered_three_expanded (f : Kind → Kind → Kind → List (List Kind)) :
    (List.finRange 11).flatMap (fun a =>
      if 0 ≤  orderKey a then
        (List.finRange 11).flatMap (fun b =>
          if orderKey a ≤  orderKey b then
            (List.finRange 11).flatMap (fun c =>
              if orderKey b ≤  orderKey c then f a b c else [])
          else [])
      else []) =
      (((f (0 : Kind) (0 : Kind) (0 : Kind) ++ f (0 : Kind) (0 : Kind) (1 : Kind) ++ f (0 : Kind) (0 : Kind) (2 : Kind) ++ f (0 : Kind) (0 : Kind) (3 : Kind) ++ f (0 : Kind) (0 : Kind) (4 : Kind) ++ f (0 : Kind) (0 : Kind) (5 : Kind) ++ f (0 : Kind) (0 : Kind) (6 : Kind) ++ f (0 : Kind) (0 : Kind) (7 : Kind) ++ f (0 : Kind) (0 : Kind) (8 : Kind) ++ f (0 : Kind) (0 : Kind) (9 : Kind) ++ f (0 : Kind) (0 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (1 : Kind) (1 : Kind) ++ f (0 : Kind) (1 : Kind) (2 : Kind) ++ f (0 : Kind) (1 : Kind) (3 : Kind) ++ f (0 : Kind) (1 : Kind) (4 : Kind) ++ f (0 : Kind) (1 : Kind) (5 : Kind) ++ f (0 : Kind) (1 : Kind) (6 : Kind) ++ f (0 : Kind) (1 : Kind) (7 : Kind) ++ f (0 : Kind) (1 : Kind) (8 : Kind) ++ f (0 : Kind) (1 : Kind) (9 : Kind) ++ f (0 : Kind) (1 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (2 : Kind) (2 : Kind) ++ f (0 : Kind) (2 : Kind) (3 : Kind) ++ f (0 : Kind) (2 : Kind) (5 : Kind) ++ f (0 : Kind) (2 : Kind) (6 : Kind) ++ f (0 : Kind) (2 : Kind) (7 : Kind) ++ f (0 : Kind) (2 : Kind) (9 : Kind) ++ f (0 : Kind) (2 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (3 : Kind) (3 : Kind) ++ f (0 : Kind) (3 : Kind) (6 : Kind) ++ f (0 : Kind) (3 : Kind) (7 : Kind) ++ f (0 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (4 : Kind) (2 : Kind) ++ f (0 : Kind) (4 : Kind) (3 : Kind) ++ f (0 : Kind) (4 : Kind) (4 : Kind) ++ f (0 : Kind) (4 : Kind) (5 : Kind) ++ f (0 : Kind) (4 : Kind) (6 : Kind) ++ f (0 : Kind) (4 : Kind) (7 : Kind) ++ f (0 : Kind) (4 : Kind) (8 : Kind) ++ f (0 : Kind) (4 : Kind) (9 : Kind) ++ f (0 : Kind) (4 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (5 : Kind) (3 : Kind) ++ f (0 : Kind) (5 : Kind) (5 : Kind) ++ f (0 : Kind) (5 : Kind) (6 : Kind) ++ f (0 : Kind) (5 : Kind) (7 : Kind) ++ f (0 : Kind) (5 : Kind) (9 : Kind) ++ f (0 : Kind) (5 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (6 : Kind) (6 : Kind) ++ f (0 : Kind) (6 : Kind) (7 : Kind) ++ f (0 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (0 : Kind) (8 : Kind) (2 : Kind) ++ f (0 : Kind) (8 : Kind) (3 : Kind) ++ f (0 : Kind) (8 : Kind) (5 : Kind) ++ f (0 : Kind) (8 : Kind) (6 : Kind) ++ f (0 : Kind) (8 : Kind) (7 : Kind) ++ f (0 : Kind) (8 : Kind) (8 : Kind) ++ f (0 : Kind) (8 : Kind) (9 : Kind) ++ f (0 : Kind) (8 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (9 : Kind) (3 : Kind) ++ f (0 : Kind) (9 : Kind) (6 : Kind) ++ f (0 : Kind) (9 : Kind) (7 : Kind) ++ f (0 : Kind) (9 : Kind) (9 : Kind) ++ f (0 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (0 : Kind) (10 : Kind) (7 : Kind) ++ f (0 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (1 : Kind) (1 : Kind) (1 : Kind) ++ f (1 : Kind) (1 : Kind) (2 : Kind) ++ f (1 : Kind) (1 : Kind) (3 : Kind) ++ f (1 : Kind) (1 : Kind) (4 : Kind) ++ f (1 : Kind) (1 : Kind) (5 : Kind) ++ f (1 : Kind) (1 : Kind) (6 : Kind) ++ f (1 : Kind) (1 : Kind) (7 : Kind) ++ f (1 : Kind) (1 : Kind) (8 : Kind) ++ f (1 : Kind) (1 : Kind) (9 : Kind) ++ f (1 : Kind) (1 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (2 : Kind) (2 : Kind) ++ f (1 : Kind) (2 : Kind) (3 : Kind) ++ f (1 : Kind) (2 : Kind) (5 : Kind) ++ f (1 : Kind) (2 : Kind) (6 : Kind) ++ f (1 : Kind) (2 : Kind) (7 : Kind) ++ f (1 : Kind) (2 : Kind) (9 : Kind) ++ f (1 : Kind) (2 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (3 : Kind) (3 : Kind) ++ f (1 : Kind) (3 : Kind) (6 : Kind) ++ f (1 : Kind) (3 : Kind) (7 : Kind) ++ f (1 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (4 : Kind) (2 : Kind) ++ f (1 : Kind) (4 : Kind) (3 : Kind) ++ f (1 : Kind) (4 : Kind) (4 : Kind) ++ f (1 : Kind) (4 : Kind) (5 : Kind) ++ f (1 : Kind) (4 : Kind) (6 : Kind) ++ f (1 : Kind) (4 : Kind) (7 : Kind) ++ f (1 : Kind) (4 : Kind) (8 : Kind) ++ f (1 : Kind) (4 : Kind) (9 : Kind) ++ f (1 : Kind) (4 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (5 : Kind) (3 : Kind) ++ f (1 : Kind) (5 : Kind) (5 : Kind) ++ f (1 : Kind) (5 : Kind) (6 : Kind) ++ f (1 : Kind) (5 : Kind) (7 : Kind) ++ f (1 : Kind) (5 : Kind) (9 : Kind) ++ f (1 : Kind) (5 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (6 : Kind) (6 : Kind) ++ f (1 : Kind) (6 : Kind) (7 : Kind) ++ f (1 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (1 : Kind) (8 : Kind) (2 : Kind) ++ f (1 : Kind) (8 : Kind) (3 : Kind) ++ f (1 : Kind) (8 : Kind) (5 : Kind) ++ f (1 : Kind) (8 : Kind) (6 : Kind) ++ f (1 : Kind) (8 : Kind) (7 : Kind) ++ f (1 : Kind) (8 : Kind) (8 : Kind) ++ f (1 : Kind) (8 : Kind) (9 : Kind) ++ f (1 : Kind) (8 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (9 : Kind) (3 : Kind) ++ f (1 : Kind) (9 : Kind) (6 : Kind) ++ f (1 : Kind) (9 : Kind) (7 : Kind) ++ f (1 : Kind) (9 : Kind) (9 : Kind) ++ f (1 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (1 : Kind) (10 : Kind) (7 : Kind) ++ f (1 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (2 : Kind) (2 : Kind) (2 : Kind) ++ f (2 : Kind) (2 : Kind) (3 : Kind) ++ f (2 : Kind) (2 : Kind) (5 : Kind) ++ f (2 : Kind) (2 : Kind) (6 : Kind) ++ f (2 : Kind) (2 : Kind) (7 : Kind) ++ f (2 : Kind) (2 : Kind) (9 : Kind) ++ f (2 : Kind) (2 : Kind) (10 : Kind) ++ []) ++ (f (2 : Kind) (3 : Kind) (3 : Kind) ++ f (2 : Kind) (3 : Kind) (6 : Kind) ++ f (2 : Kind) (3 : Kind) (7 : Kind) ++ f (2 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (2 : Kind) (5 : Kind) (3 : Kind) ++ f (2 : Kind) (5 : Kind) (5 : Kind) ++ f (2 : Kind) (5 : Kind) (6 : Kind) ++ f (2 : Kind) (5 : Kind) (7 : Kind) ++ f (2 : Kind) (5 : Kind) (9 : Kind) ++ f (2 : Kind) (5 : Kind) (10 : Kind) ++ []) ++ (f (2 : Kind) (6 : Kind) (6 : Kind) ++ f (2 : Kind) (6 : Kind) (7 : Kind) ++ f (2 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (2 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (2 : Kind) (9 : Kind) (3 : Kind) ++ f (2 : Kind) (9 : Kind) (6 : Kind) ++ f (2 : Kind) (9 : Kind) (7 : Kind) ++ f (2 : Kind) (9 : Kind) (9 : Kind) ++ f (2 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (2 : Kind) (10 : Kind) (7 : Kind) ++ f (2 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (3 : Kind) (3 : Kind) (3 : Kind) ++ f (3 : Kind) (3 : Kind) (6 : Kind) ++ f (3 : Kind) (3 : Kind) (7 : Kind) ++ f (3 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (3 : Kind) (6 : Kind) (6 : Kind) ++ f (3 : Kind) (6 : Kind) (7 : Kind) ++ f (3 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (3 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (3 : Kind) (10 : Kind) (7 : Kind) ++ f (3 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (4 : Kind) (2 : Kind) (2 : Kind) ++ f (4 : Kind) (2 : Kind) (3 : Kind) ++ f (4 : Kind) (2 : Kind) (5 : Kind) ++ f (4 : Kind) (2 : Kind) (6 : Kind) ++ f (4 : Kind) (2 : Kind) (7 : Kind) ++ f (4 : Kind) (2 : Kind) (9 : Kind) ++ f (4 : Kind) (2 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (3 : Kind) (3 : Kind) ++ f (4 : Kind) (3 : Kind) (6 : Kind) ++ f (4 : Kind) (3 : Kind) (7 : Kind) ++ f (4 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (4 : Kind) (2 : Kind) ++ f (4 : Kind) (4 : Kind) (3 : Kind) ++ f (4 : Kind) (4 : Kind) (4 : Kind) ++ f (4 : Kind) (4 : Kind) (5 : Kind) ++ f (4 : Kind) (4 : Kind) (6 : Kind) ++ f (4 : Kind) (4 : Kind) (7 : Kind) ++ f (4 : Kind) (4 : Kind) (8 : Kind) ++ f (4 : Kind) (4 : Kind) (9 : Kind) ++ f (4 : Kind) (4 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (5 : Kind) (3 : Kind) ++ f (4 : Kind) (5 : Kind) (5 : Kind) ++ f (4 : Kind) (5 : Kind) (6 : Kind) ++ f (4 : Kind) (5 : Kind) (7 : Kind) ++ f (4 : Kind) (5 : Kind) (9 : Kind) ++ f (4 : Kind) (5 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (6 : Kind) (6 : Kind) ++ f (4 : Kind) (6 : Kind) (7 : Kind) ++ f (4 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (4 : Kind) (8 : Kind) (2 : Kind) ++ f (4 : Kind) (8 : Kind) (3 : Kind) ++ f (4 : Kind) (8 : Kind) (5 : Kind) ++ f (4 : Kind) (8 : Kind) (6 : Kind) ++ f (4 : Kind) (8 : Kind) (7 : Kind) ++ f (4 : Kind) (8 : Kind) (8 : Kind) ++ f (4 : Kind) (8 : Kind) (9 : Kind) ++ f (4 : Kind) (8 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (9 : Kind) (3 : Kind) ++ f (4 : Kind) (9 : Kind) (6 : Kind) ++ f (4 : Kind) (9 : Kind) (7 : Kind) ++ f (4 : Kind) (9 : Kind) (9 : Kind) ++ f (4 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (4 : Kind) (10 : Kind) (7 : Kind) ++ f (4 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (5 : Kind) (3 : Kind) (3 : Kind) ++ f (5 : Kind) (3 : Kind) (6 : Kind) ++ f (5 : Kind) (3 : Kind) (7 : Kind) ++ f (5 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (5 : Kind) (5 : Kind) (3 : Kind) ++ f (5 : Kind) (5 : Kind) (5 : Kind) ++ f (5 : Kind) (5 : Kind) (6 : Kind) ++ f (5 : Kind) (5 : Kind) (7 : Kind) ++ f (5 : Kind) (5 : Kind) (9 : Kind) ++ f (5 : Kind) (5 : Kind) (10 : Kind) ++ []) ++ (f (5 : Kind) (6 : Kind) (6 : Kind) ++ f (5 : Kind) (6 : Kind) (7 : Kind) ++ f (5 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (5 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (5 : Kind) (9 : Kind) (3 : Kind) ++ f (5 : Kind) (9 : Kind) (6 : Kind) ++ f (5 : Kind) (9 : Kind) (7 : Kind) ++ f (5 : Kind) (9 : Kind) (9 : Kind) ++ f (5 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (5 : Kind) (10 : Kind) (7 : Kind) ++ f (5 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (6 : Kind) (6 : Kind) (6 : Kind) ++ f (6 : Kind) (6 : Kind) (7 : Kind) ++ f (6 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (6 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (6 : Kind) (10 : Kind) (7 : Kind) ++ f (6 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (7 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ []) ++ ((f (8 : Kind) (2 : Kind) (2 : Kind) ++ f (8 : Kind) (2 : Kind) (3 : Kind) ++ f (8 : Kind) (2 : Kind) (5 : Kind) ++ f (8 : Kind) (2 : Kind) (6 : Kind) ++ f (8 : Kind) (2 : Kind) (7 : Kind) ++ f (8 : Kind) (2 : Kind) (9 : Kind) ++ f (8 : Kind) (2 : Kind) (10 : Kind) ++ []) ++ (f (8 : Kind) (3 : Kind) (3 : Kind) ++ f (8 : Kind) (3 : Kind) (6 : Kind) ++ f (8 : Kind) (3 : Kind) (7 : Kind) ++ f (8 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (8 : Kind) (5 : Kind) (3 : Kind) ++ f (8 : Kind) (5 : Kind) (5 : Kind) ++ f (8 : Kind) (5 : Kind) (6 : Kind) ++ f (8 : Kind) (5 : Kind) (7 : Kind) ++ f (8 : Kind) (5 : Kind) (9 : Kind) ++ f (8 : Kind) (5 : Kind) (10 : Kind) ++ []) ++ (f (8 : Kind) (6 : Kind) (6 : Kind) ++ f (8 : Kind) (6 : Kind) (7 : Kind) ++ f (8 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (8 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (8 : Kind) (8 : Kind) (2 : Kind) ++ f (8 : Kind) (8 : Kind) (3 : Kind) ++ f (8 : Kind) (8 : Kind) (5 : Kind) ++ f (8 : Kind) (8 : Kind) (6 : Kind) ++ f (8 : Kind) (8 : Kind) (7 : Kind) ++ f (8 : Kind) (8 : Kind) (8 : Kind) ++ f (8 : Kind) (8 : Kind) (9 : Kind) ++ f (8 : Kind) (8 : Kind) (10 : Kind) ++ []) ++ (f (8 : Kind) (9 : Kind) (3 : Kind) ++ f (8 : Kind) (9 : Kind) (6 : Kind) ++ f (8 : Kind) (9 : Kind) (7 : Kind) ++ f (8 : Kind) (9 : Kind) (9 : Kind) ++ f (8 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (8 : Kind) (10 : Kind) (7 : Kind) ++ f (8 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (9 : Kind) (3 : Kind) (3 : Kind) ++ f (9 : Kind) (3 : Kind) (6 : Kind) ++ f (9 : Kind) (3 : Kind) (7 : Kind) ++ f (9 : Kind) (3 : Kind) (10 : Kind) ++ []) ++ (f (9 : Kind) (6 : Kind) (6 : Kind) ++ f (9 : Kind) (6 : Kind) (7 : Kind) ++ f (9 : Kind) (6 : Kind) (10 : Kind) ++ []) ++ (f (9 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (9 : Kind) (9 : Kind) (3 : Kind) ++ f (9 : Kind) (9 : Kind) (6 : Kind) ++ f (9 : Kind) (9 : Kind) (7 : Kind) ++ f (9 : Kind) (9 : Kind) (9 : Kind) ++ f (9 : Kind) (9 : Kind) (10 : Kind) ++ []) ++ (f (9 : Kind) (10 : Kind) (7 : Kind) ++ f (9 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ ((f (10 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ (f (10 : Kind) (10 : Kind) (7 : Kind) ++ f (10 : Kind) (10 : Kind) (10 : Kind) ++ []) ++ []) ++ []) := by
  change (((f (0 : Kind) (0 : Kind) (0 : Kind) ++ (f (0 : Kind) (0 : Kind) (1 : Kind) ++ (f (0 : Kind) (0 : Kind) (2 : Kind) ++ (f (0 : Kind) (0 : Kind) (3 : Kind) ++ (f (0 : Kind) (0 : Kind) (4 : Kind) ++ (f (0 : Kind) (0 : Kind) (5 : Kind) ++ (f (0 : Kind) (0 : Kind) (6 : Kind) ++ (f (0 : Kind) (0 : Kind) (7 : Kind) ++ (f (0 : Kind) (0 : Kind) (8 : Kind) ++ (f (0 : Kind) (0 : Kind) (9 : Kind) ++ (f (0 : Kind) (0 : Kind) (10 : Kind) ++ []))))))))))) ++ ((f (0 : Kind) (1 : Kind) (1 : Kind) ++ (f (0 : Kind) (1 : Kind) (2 : Kind) ++ (f (0 : Kind) (1 : Kind) (3 : Kind) ++ (f (0 : Kind) (1 : Kind) (4 : Kind) ++ (f (0 : Kind) (1 : Kind) (5 : Kind) ++ (f (0 : Kind) (1 : Kind) (6 : Kind) ++ (f (0 : Kind) (1 : Kind) (7 : Kind) ++ (f (0 : Kind) (1 : Kind) (8 : Kind) ++ (f (0 : Kind) (1 : Kind) (9 : Kind) ++ (f (0 : Kind) (1 : Kind) (10 : Kind) ++ [])))))))))) ++ ((f (0 : Kind) (2 : Kind) (2 : Kind) ++ (f (0 : Kind) (2 : Kind) (3 : Kind) ++ (f (0 : Kind) (2 : Kind) (5 : Kind) ++ (f (0 : Kind) (2 : Kind) (6 : Kind) ++ (f (0 : Kind) (2 : Kind) (7 : Kind) ++ (f (0 : Kind) (2 : Kind) (9 : Kind) ++ (f (0 : Kind) (2 : Kind) (10 : Kind) ++ []))))))) ++ ((f (0 : Kind) (3 : Kind) (3 : Kind) ++ (f (0 : Kind) (3 : Kind) (6 : Kind) ++ (f (0 : Kind) (3 : Kind) (7 : Kind) ++ (f (0 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (0 : Kind) (4 : Kind) (2 : Kind) ++ (f (0 : Kind) (4 : Kind) (3 : Kind) ++ (f (0 : Kind) (4 : Kind) (4 : Kind) ++ (f (0 : Kind) (4 : Kind) (5 : Kind) ++ (f (0 : Kind) (4 : Kind) (6 : Kind) ++ (f (0 : Kind) (4 : Kind) (7 : Kind) ++ (f (0 : Kind) (4 : Kind) (8 : Kind) ++ (f (0 : Kind) (4 : Kind) (9 : Kind) ++ (f (0 : Kind) (4 : Kind) (10 : Kind) ++ []))))))))) ++ ((f (0 : Kind) (5 : Kind) (3 : Kind) ++ (f (0 : Kind) (5 : Kind) (5 : Kind) ++ (f (0 : Kind) (5 : Kind) (6 : Kind) ++ (f (0 : Kind) (5 : Kind) (7 : Kind) ++ (f (0 : Kind) (5 : Kind) (9 : Kind) ++ (f (0 : Kind) (5 : Kind) (10 : Kind) ++ [])))))) ++ ((f (0 : Kind) (6 : Kind) (6 : Kind) ++ (f (0 : Kind) (6 : Kind) (7 : Kind) ++ (f (0 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (0 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (0 : Kind) (8 : Kind) (2 : Kind) ++ (f (0 : Kind) (8 : Kind) (3 : Kind) ++ (f (0 : Kind) (8 : Kind) (5 : Kind) ++ (f (0 : Kind) (8 : Kind) (6 : Kind) ++ (f (0 : Kind) (8 : Kind) (7 : Kind) ++ (f (0 : Kind) (8 : Kind) (8 : Kind) ++ (f (0 : Kind) (8 : Kind) (9 : Kind) ++ (f (0 : Kind) (8 : Kind) (10 : Kind) ++ [])))))))) ++ ((f (0 : Kind) (9 : Kind) (3 : Kind) ++ (f (0 : Kind) (9 : Kind) (6 : Kind) ++ (f (0 : Kind) (9 : Kind) (7 : Kind) ++ (f (0 : Kind) (9 : Kind) (9 : Kind) ++ (f (0 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (0 : Kind) (10 : Kind) (7 : Kind) ++ (f (0 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ []))))))))))) ++ (((f (1 : Kind) (1 : Kind) (1 : Kind) ++ (f (1 : Kind) (1 : Kind) (2 : Kind) ++ (f (1 : Kind) (1 : Kind) (3 : Kind) ++ (f (1 : Kind) (1 : Kind) (4 : Kind) ++ (f (1 : Kind) (1 : Kind) (5 : Kind) ++ (f (1 : Kind) (1 : Kind) (6 : Kind) ++ (f (1 : Kind) (1 : Kind) (7 : Kind) ++ (f (1 : Kind) (1 : Kind) (8 : Kind) ++ (f (1 : Kind) (1 : Kind) (9 : Kind) ++ (f (1 : Kind) (1 : Kind) (10 : Kind) ++ [])))))))))) ++ ((f (1 : Kind) (2 : Kind) (2 : Kind) ++ (f (1 : Kind) (2 : Kind) (3 : Kind) ++ (f (1 : Kind) (2 : Kind) (5 : Kind) ++ (f (1 : Kind) (2 : Kind) (6 : Kind) ++ (f (1 : Kind) (2 : Kind) (7 : Kind) ++ (f (1 : Kind) (2 : Kind) (9 : Kind) ++ (f (1 : Kind) (2 : Kind) (10 : Kind) ++ []))))))) ++ ((f (1 : Kind) (3 : Kind) (3 : Kind) ++ (f (1 : Kind) (3 : Kind) (6 : Kind) ++ (f (1 : Kind) (3 : Kind) (7 : Kind) ++ (f (1 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (1 : Kind) (4 : Kind) (2 : Kind) ++ (f (1 : Kind) (4 : Kind) (3 : Kind) ++ (f (1 : Kind) (4 : Kind) (4 : Kind) ++ (f (1 : Kind) (4 : Kind) (5 : Kind) ++ (f (1 : Kind) (4 : Kind) (6 : Kind) ++ (f (1 : Kind) (4 : Kind) (7 : Kind) ++ (f (1 : Kind) (4 : Kind) (8 : Kind) ++ (f (1 : Kind) (4 : Kind) (9 : Kind) ++ (f (1 : Kind) (4 : Kind) (10 : Kind) ++ []))))))))) ++ ((f (1 : Kind) (5 : Kind) (3 : Kind) ++ (f (1 : Kind) (5 : Kind) (5 : Kind) ++ (f (1 : Kind) (5 : Kind) (6 : Kind) ++ (f (1 : Kind) (5 : Kind) (7 : Kind) ++ (f (1 : Kind) (5 : Kind) (9 : Kind) ++ (f (1 : Kind) (5 : Kind) (10 : Kind) ++ [])))))) ++ ((f (1 : Kind) (6 : Kind) (6 : Kind) ++ (f (1 : Kind) (6 : Kind) (7 : Kind) ++ (f (1 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (1 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (1 : Kind) (8 : Kind) (2 : Kind) ++ (f (1 : Kind) (8 : Kind) (3 : Kind) ++ (f (1 : Kind) (8 : Kind) (5 : Kind) ++ (f (1 : Kind) (8 : Kind) (6 : Kind) ++ (f (1 : Kind) (8 : Kind) (7 : Kind) ++ (f (1 : Kind) (8 : Kind) (8 : Kind) ++ (f (1 : Kind) (8 : Kind) (9 : Kind) ++ (f (1 : Kind) (8 : Kind) (10 : Kind) ++ [])))))))) ++ ((f (1 : Kind) (9 : Kind) (3 : Kind) ++ (f (1 : Kind) (9 : Kind) (6 : Kind) ++ (f (1 : Kind) (9 : Kind) (7 : Kind) ++ (f (1 : Kind) (9 : Kind) (9 : Kind) ++ (f (1 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (1 : Kind) (10 : Kind) (7 : Kind) ++ (f (1 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ [])))))))))) ++ (((f (2 : Kind) (2 : Kind) (2 : Kind) ++ (f (2 : Kind) (2 : Kind) (3 : Kind) ++ (f (2 : Kind) (2 : Kind) (5 : Kind) ++ (f (2 : Kind) (2 : Kind) (6 : Kind) ++ (f (2 : Kind) (2 : Kind) (7 : Kind) ++ (f (2 : Kind) (2 : Kind) (9 : Kind) ++ (f (2 : Kind) (2 : Kind) (10 : Kind) ++ []))))))) ++ ((f (2 : Kind) (3 : Kind) (3 : Kind) ++ (f (2 : Kind) (3 : Kind) (6 : Kind) ++ (f (2 : Kind) (3 : Kind) (7 : Kind) ++ (f (2 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (2 : Kind) (5 : Kind) (3 : Kind) ++ (f (2 : Kind) (5 : Kind) (5 : Kind) ++ (f (2 : Kind) (5 : Kind) (6 : Kind) ++ (f (2 : Kind) (5 : Kind) (7 : Kind) ++ (f (2 : Kind) (5 : Kind) (9 : Kind) ++ (f (2 : Kind) (5 : Kind) (10 : Kind) ++ [])))))) ++ ((f (2 : Kind) (6 : Kind) (6 : Kind) ++ (f (2 : Kind) (6 : Kind) (7 : Kind) ++ (f (2 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (2 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (2 : Kind) (9 : Kind) (3 : Kind) ++ (f (2 : Kind) (9 : Kind) (6 : Kind) ++ (f (2 : Kind) (9 : Kind) (7 : Kind) ++ (f (2 : Kind) (9 : Kind) (9 : Kind) ++ (f (2 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (2 : Kind) (10 : Kind) (7 : Kind) ++ (f (2 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ []))))))) ++ (((f (3 : Kind) (3 : Kind) (3 : Kind) ++ (f (3 : Kind) (3 : Kind) (6 : Kind) ++ (f (3 : Kind) (3 : Kind) (7 : Kind) ++ (f (3 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (3 : Kind) (6 : Kind) (6 : Kind) ++ (f (3 : Kind) (6 : Kind) (7 : Kind) ++ (f (3 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (3 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (3 : Kind) (10 : Kind) (7 : Kind) ++ (f (3 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ [])))) ++ (((f (4 : Kind) (2 : Kind) (2 : Kind) ++ (f (4 : Kind) (2 : Kind) (3 : Kind) ++ (f (4 : Kind) (2 : Kind) (5 : Kind) ++ (f (4 : Kind) (2 : Kind) (6 : Kind) ++ (f (4 : Kind) (2 : Kind) (7 : Kind) ++ (f (4 : Kind) (2 : Kind) (9 : Kind) ++ (f (4 : Kind) (2 : Kind) (10 : Kind) ++ []))))))) ++ ((f (4 : Kind) (3 : Kind) (3 : Kind) ++ (f (4 : Kind) (3 : Kind) (6 : Kind) ++ (f (4 : Kind) (3 : Kind) (7 : Kind) ++ (f (4 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (4 : Kind) (4 : Kind) (2 : Kind) ++ (f (4 : Kind) (4 : Kind) (3 : Kind) ++ (f (4 : Kind) (4 : Kind) (4 : Kind) ++ (f (4 : Kind) (4 : Kind) (5 : Kind) ++ (f (4 : Kind) (4 : Kind) (6 : Kind) ++ (f (4 : Kind) (4 : Kind) (7 : Kind) ++ (f (4 : Kind) (4 : Kind) (8 : Kind) ++ (f (4 : Kind) (4 : Kind) (9 : Kind) ++ (f (4 : Kind) (4 : Kind) (10 : Kind) ++ []))))))))) ++ ((f (4 : Kind) (5 : Kind) (3 : Kind) ++ (f (4 : Kind) (5 : Kind) (5 : Kind) ++ (f (4 : Kind) (5 : Kind) (6 : Kind) ++ (f (4 : Kind) (5 : Kind) (7 : Kind) ++ (f (4 : Kind) (5 : Kind) (9 : Kind) ++ (f (4 : Kind) (5 : Kind) (10 : Kind) ++ [])))))) ++ ((f (4 : Kind) (6 : Kind) (6 : Kind) ++ (f (4 : Kind) (6 : Kind) (7 : Kind) ++ (f (4 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (4 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (4 : Kind) (8 : Kind) (2 : Kind) ++ (f (4 : Kind) (8 : Kind) (3 : Kind) ++ (f (4 : Kind) (8 : Kind) (5 : Kind) ++ (f (4 : Kind) (8 : Kind) (6 : Kind) ++ (f (4 : Kind) (8 : Kind) (7 : Kind) ++ (f (4 : Kind) (8 : Kind) (8 : Kind) ++ (f (4 : Kind) (8 : Kind) (9 : Kind) ++ (f (4 : Kind) (8 : Kind) (10 : Kind) ++ [])))))))) ++ ((f (4 : Kind) (9 : Kind) (3 : Kind) ++ (f (4 : Kind) (9 : Kind) (6 : Kind) ++ (f (4 : Kind) (9 : Kind) (7 : Kind) ++ (f (4 : Kind) (9 : Kind) (9 : Kind) ++ (f (4 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (4 : Kind) (10 : Kind) (7 : Kind) ++ (f (4 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ []))))))))) ++ (((f (5 : Kind) (3 : Kind) (3 : Kind) ++ (f (5 : Kind) (3 : Kind) (6 : Kind) ++ (f (5 : Kind) (3 : Kind) (7 : Kind) ++ (f (5 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (5 : Kind) (5 : Kind) (3 : Kind) ++ (f (5 : Kind) (5 : Kind) (5 : Kind) ++ (f (5 : Kind) (5 : Kind) (6 : Kind) ++ (f (5 : Kind) (5 : Kind) (7 : Kind) ++ (f (5 : Kind) (5 : Kind) (9 : Kind) ++ (f (5 : Kind) (5 : Kind) (10 : Kind) ++ [])))))) ++ ((f (5 : Kind) (6 : Kind) (6 : Kind) ++ (f (5 : Kind) (6 : Kind) (7 : Kind) ++ (f (5 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (5 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (5 : Kind) (9 : Kind) (3 : Kind) ++ (f (5 : Kind) (9 : Kind) (6 : Kind) ++ (f (5 : Kind) (9 : Kind) (7 : Kind) ++ (f (5 : Kind) (9 : Kind) (9 : Kind) ++ (f (5 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (5 : Kind) (10 : Kind) (7 : Kind) ++ (f (5 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ [])))))) ++ (((f (6 : Kind) (6 : Kind) (6 : Kind) ++ (f (6 : Kind) (6 : Kind) (7 : Kind) ++ (f (6 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (6 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (6 : Kind) (10 : Kind) (7 : Kind) ++ (f (6 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ []))) ++ (((f (7 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ []) ++ (((f (8 : Kind) (2 : Kind) (2 : Kind) ++ (f (8 : Kind) (2 : Kind) (3 : Kind) ++ (f (8 : Kind) (2 : Kind) (5 : Kind) ++ (f (8 : Kind) (2 : Kind) (6 : Kind) ++ (f (8 : Kind) (2 : Kind) (7 : Kind) ++ (f (8 : Kind) (2 : Kind) (9 : Kind) ++ (f (8 : Kind) (2 : Kind) (10 : Kind) ++ []))))))) ++ ((f (8 : Kind) (3 : Kind) (3 : Kind) ++ (f (8 : Kind) (3 : Kind) (6 : Kind) ++ (f (8 : Kind) (3 : Kind) (7 : Kind) ++ (f (8 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (8 : Kind) (5 : Kind) (3 : Kind) ++ (f (8 : Kind) (5 : Kind) (5 : Kind) ++ (f (8 : Kind) (5 : Kind) (6 : Kind) ++ (f (8 : Kind) (5 : Kind) (7 : Kind) ++ (f (8 : Kind) (5 : Kind) (9 : Kind) ++ (f (8 : Kind) (5 : Kind) (10 : Kind) ++ [])))))) ++ ((f (8 : Kind) (6 : Kind) (6 : Kind) ++ (f (8 : Kind) (6 : Kind) (7 : Kind) ++ (f (8 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (8 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (8 : Kind) (8 : Kind) (2 : Kind) ++ (f (8 : Kind) (8 : Kind) (3 : Kind) ++ (f (8 : Kind) (8 : Kind) (5 : Kind) ++ (f (8 : Kind) (8 : Kind) (6 : Kind) ++ (f (8 : Kind) (8 : Kind) (7 : Kind) ++ (f (8 : Kind) (8 : Kind) (8 : Kind) ++ (f (8 : Kind) (8 : Kind) (9 : Kind) ++ (f (8 : Kind) (8 : Kind) (10 : Kind) ++ [])))))))) ++ ((f (8 : Kind) (9 : Kind) (3 : Kind) ++ (f (8 : Kind) (9 : Kind) (6 : Kind) ++ (f (8 : Kind) (9 : Kind) (7 : Kind) ++ (f (8 : Kind) (9 : Kind) (9 : Kind) ++ (f (8 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (8 : Kind) (10 : Kind) (7 : Kind) ++ (f (8 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ [])))))))) ++ (((f (9 : Kind) (3 : Kind) (3 : Kind) ++ (f (9 : Kind) (3 : Kind) (6 : Kind) ++ (f (9 : Kind) (3 : Kind) (7 : Kind) ++ (f (9 : Kind) (3 : Kind) (10 : Kind) ++ [])))) ++ ((f (9 : Kind) (6 : Kind) (6 : Kind) ++ (f (9 : Kind) (6 : Kind) (7 : Kind) ++ (f (9 : Kind) (6 : Kind) (10 : Kind) ++ []))) ++ ((f (9 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (9 : Kind) (9 : Kind) (3 : Kind) ++ (f (9 : Kind) (9 : Kind) (6 : Kind) ++ (f (9 : Kind) (9 : Kind) (7 : Kind) ++ (f (9 : Kind) (9 : Kind) (9 : Kind) ++ (f (9 : Kind) (9 : Kind) (10 : Kind) ++ []))))) ++ ((f (9 : Kind) (10 : Kind) (7 : Kind) ++ (f (9 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ []))))) ++ (((f (10 : Kind) (7 : Kind) (7 : Kind) ++ []) ++ ((f (10 : Kind) (10 : Kind) (7 : Kind) ++ (f (10 : Kind) (10 : Kind) (10 : Kind) ++ [])) ++ [])) ++ []))))))))))) = _
  simp only [List.append_assoc, List.nil_append, List.append_nil]

theorem filteredPrefix_three_expanded (n : ℕ) :
    filteredPrefix [] 0 (n+3) =
      (((filteredPrefix ([0,0,0] : List Kind) (orderKey (0 : Kind)) n ++ filteredPrefix ([0,0,1] : List Kind) (orderKey (1 : Kind)) n ++ filteredPrefix ([0,0,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([0,0,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,0,4] : List Kind) (orderKey (4 : Kind)) n ++ filteredPrefix ([0,0,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([0,0,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,0,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,0,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([0,0,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,0,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,1,1] : List Kind) (orderKey (1 : Kind)) n ++ filteredPrefix ([0,1,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([0,1,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,1,4] : List Kind) (orderKey (4 : Kind)) n ++ filteredPrefix ([0,1,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([0,1,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,1,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,1,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([0,1,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,1,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,2,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([0,2,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,2,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([0,2,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,2,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,2,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,2,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,4,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([0,4,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,4,4] : List Kind) (orderKey (4 : Kind)) n ++ filteredPrefix ([0,4,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([0,4,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,4,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,4,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([0,4,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,4,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,5,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,5,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([0,5,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,5,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,5,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,5,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([0,8,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([0,8,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,8,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([0,8,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,8,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,8,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([0,8,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,8,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([0,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([0,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([0,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([0,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([0,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([1,1,1] : List Kind) (orderKey (1 : Kind)) n ++ filteredPrefix ([1,1,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([1,1,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,1,4] : List Kind) (orderKey (4 : Kind)) n ++ filteredPrefix ([1,1,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([1,1,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,1,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,1,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([1,1,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([1,1,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,2,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([1,2,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,2,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([1,2,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,2,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,2,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([1,2,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,4,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([1,4,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,4,4] : List Kind) (orderKey (4 : Kind)) n ++ filteredPrefix ([1,4,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([1,4,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,4,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,4,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([1,4,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([1,4,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,5,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,5,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([1,5,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,5,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,5,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([1,5,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([1,8,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([1,8,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,8,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([1,8,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,8,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,8,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([1,8,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([1,8,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([1,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([1,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([1,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([1,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([1,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([2,2,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([2,2,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([2,2,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([2,2,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([2,2,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([2,2,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([2,2,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([2,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([2,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([2,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([2,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([2,5,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([2,5,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([2,5,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([2,5,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([2,5,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([2,5,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([2,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([2,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([2,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([2,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([2,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([2,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([2,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([2,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([2,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([2,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([2,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([3,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([3,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([3,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([3,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([3,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([3,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([3,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([3,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([3,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([3,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([4,2,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([4,2,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([4,2,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([4,2,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,2,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,2,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([4,2,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([4,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,4,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([4,4,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([4,4,4] : List Kind) (orderKey (4 : Kind)) n ++ filteredPrefix ([4,4,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([4,4,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,4,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,4,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([4,4,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([4,4,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,5,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([4,5,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([4,5,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,5,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,5,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([4,5,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([4,8,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([4,8,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([4,8,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([4,8,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,8,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,8,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([4,8,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([4,8,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([4,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([4,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([4,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([4,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([4,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([5,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([5,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([5,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([5,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([5,5,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([5,5,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([5,5,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([5,5,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([5,5,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([5,5,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([5,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([5,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([5,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([5,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([5,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([5,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([5,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([5,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([5,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([5,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([5,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([6,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([6,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([6,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([6,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([6,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([6,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([7,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([8,2,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([8,2,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([8,2,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([8,2,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([8,2,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,2,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([8,2,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([8,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([8,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([8,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([8,5,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([8,5,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([8,5,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([8,5,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,5,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([8,5,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([8,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([8,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([8,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([8,8,2] : List Kind) (orderKey (2 : Kind)) n ++ filteredPrefix ([8,8,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([8,8,5] : List Kind) (orderKey (5 : Kind)) n ++ filteredPrefix ([8,8,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([8,8,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,8,8] : List Kind) (orderKey (8 : Kind)) n ++ filteredPrefix ([8,8,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([8,8,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([8,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([8,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([8,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([8,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([8,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([8,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([9,3,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([9,3,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([9,3,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([9,3,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([9,6,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([9,6,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([9,6,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([9,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([9,9,3] : List Kind) (orderKey (3 : Kind)) n ++ filteredPrefix ([9,9,6] : List Kind) (orderKey (6 : Kind)) n ++ filteredPrefix ([9,9,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([9,9,9] : List Kind) (orderKey (9 : Kind)) n ++ filteredPrefix ([9,9,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ (filteredPrefix ([9,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([9,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ ((filteredPrefix ([10,7,7] : List Kind) (orderKey (7 : Kind)) n ++ []) ++ (filteredPrefix ([10,10,7] : List Kind) (orderKey (7 : Kind)) n ++ filteredPrefix ([10,10,10] : List Kind) (orderKey (10 : Kind)) n ++ []) ++ []) ++ []) := by
  rw [filteredPrefix_three]
  exact ordered_three_expanded
    (fun a b c => filteredPrefix ([] ++ [a,b,c]) (orderKey c) n)

end ThreeBoundEndpoint22TypeSplit



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Bounded exact type-list checks. The final theorem has the original type. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Types
open ThreeBoundQ3 ThreeBoundEndpoint22TypeSplit

private theorem type8_prefix_000 :
    filteredPrefix ([0,0,0] : List Kind) (orderKey (0 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,0] : List Kind)
    (orderKey (0 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_001 :
    filteredPrefix ([0,0,1] : List Kind) (orderKey (1 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,1] : List Kind)
    (orderKey (1 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_002 :
    filteredPrefix ([0,0,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_003 :
    filteredPrefix ([0,0,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_004 :
    filteredPrefix ([0,0,4] : List Kind) (orderKey (4 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,4] : List Kind)
    (orderKey (4 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_005 :
    filteredPrefix ([0,0,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_006 :
    filteredPrefix ([0,0,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_007 :
    filteredPrefix ([0,0,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_008 :
    filteredPrefix ([0,0,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_009 :
    filteredPrefix ([0,0,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_010 :
    filteredPrefix ([0,0,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,0,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_011 :
    filteredPrefix ([0,1,1] : List Kind) (orderKey (1 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,1,1] : List Kind)
    (orderKey (1 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_012 :
    filteredPrefix ([0,1,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_013 :
    filteredPrefix ([0,1,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_014 :
    filteredPrefix ([0,1,4] : List Kind) (orderKey (4 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,1,4] : List Kind)
    (orderKey (4 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_015 :
    filteredPrefix ([0,1,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_016 :
    filteredPrefix ([0,1,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_017 :
    filteredPrefix ([0,1,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_018 :
    filteredPrefix ([0,1,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,1,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_019 :
    filteredPrefix ([0,1,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_020 :
    filteredPrefix ([0,1,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,1,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_021 :
    filteredPrefix ([0,2,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_022 :
    filteredPrefix ([0,2,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_023 :
    filteredPrefix ([0,2,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_024 :
    filteredPrefix ([0,2,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_025 :
    filteredPrefix ([0,2,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_026 :
    filteredPrefix ([0,2,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_027 :
    filteredPrefix ([0,2,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,2,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_028 :
    filteredPrefix ([0,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,3,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_029 :
    filteredPrefix ([0,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,3,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_030 :
    filteredPrefix ([0,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,3,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_031 :
    filteredPrefix ([0,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,3,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_032 :
    filteredPrefix ([0,4,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_033 :
    filteredPrefix ([0,4,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_034 :
    filteredPrefix ([0,4,4] : List Kind) (orderKey (4 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,4,4] : List Kind)
    (orderKey (4 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_035 :
    filteredPrefix ([0,4,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_036 :
    filteredPrefix ([0,4,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_037 :
    filteredPrefix ([0,4,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_038 :
    filteredPrefix ([0,4,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,4,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_039 :
    filteredPrefix ([0,4,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_040 :
    filteredPrefix ([0,4,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,4,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_041 :
    filteredPrefix ([0,5,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,5,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_042 :
    filteredPrefix ([0,5,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,5,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_043 :
    filteredPrefix ([0,5,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,5,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_044 :
    filteredPrefix ([0,5,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,5,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_045 :
    filteredPrefix ([0,5,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,5,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_046 :
    filteredPrefix ([0,5,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,5,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_047 :
    filteredPrefix ([0,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,6,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_048 :
    filteredPrefix ([0,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,6,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_049 :
    filteredPrefix ([0,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,6,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_050 :
    filteredPrefix ([0,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[0,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_051 :
    filteredPrefix ([0,8,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_052 :
    filteredPrefix ([0,8,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_053 :
    filteredPrefix ([0,8,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_054 :
    filteredPrefix ([0,8,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_055 :
    filteredPrefix ([0,8,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_056 :
    filteredPrefix ([0,8,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_not_allowed ([0,8,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_057 :
    filteredPrefix ([0,8,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_058 :
    filteredPrefix ([0,8,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,8,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_059 :
    filteredPrefix ([0,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_060 :
    filteredPrefix ([0,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_061 :
    filteredPrefix ([0,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,9,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_062 :
    filteredPrefix ([0,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_063 :
    filteredPrefix ([0,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_064 :
    filteredPrefix ([0,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,10,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_065 :
    filteredPrefix ([0,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([0,10,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_066 :
    filteredPrefix ([1,1,1] : List Kind) (orderKey (1 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,1] : List Kind)
    (orderKey (1 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_067 :
    filteredPrefix ([1,1,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_068 :
    filteredPrefix ([1,1,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_069 :
    filteredPrefix ([1,1,4] : List Kind) (orderKey (4 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,4] : List Kind)
    (orderKey (4 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_070 :
    filteredPrefix ([1,1,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_071 :
    filteredPrefix ([1,1,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_072 :
    filteredPrefix ([1,1,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_073 :
    filteredPrefix ([1,1,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_074 :
    filteredPrefix ([1,1,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_075 :
    filteredPrefix ([1,1,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_076 :
    filteredPrefix ([1,2,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_077 :
    filteredPrefix ([1,2,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_078 :
    filteredPrefix ([1,2,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_079 :
    filteredPrefix ([1,2,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_080 :
    filteredPrefix ([1,2,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_081 :
    filteredPrefix ([1,2,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_082 :
    filteredPrefix ([1,2,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,2,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_083 :
    filteredPrefix ([1,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,3,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_084 :
    filteredPrefix ([1,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,3,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_085 :
    filteredPrefix ([1,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[1,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_086 :
    filteredPrefix ([1,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,3,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_087 :
    filteredPrefix ([1,4,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_088 :
    filteredPrefix ([1,4,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_089 :
    filteredPrefix ([1,4,4] : List Kind) (orderKey (4 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,4] : List Kind)
    (orderKey (4 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_090 :
    filteredPrefix ([1,4,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_091 :
    filteredPrefix ([1,4,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_092 :
    filteredPrefix ([1,4,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_093 :
    filteredPrefix ([1,4,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_094 :
    filteredPrefix ([1,4,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_095 :
    filteredPrefix ([1,4,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_096 :
    filteredPrefix ([1,5,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,5,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_097 :
    filteredPrefix ([1,5,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,5,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_098 :
    filteredPrefix ([1,5,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,5,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_099 :
    filteredPrefix ([1,5,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,5,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_100 :
    filteredPrefix ([1,5,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,5,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_101 :
    filteredPrefix ([1,5,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,5,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_102 :
    filteredPrefix ([1,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,6,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_103 :
    filteredPrefix ([1,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[1,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_104 :
    filteredPrefix ([1,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,6,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_105 :
    filteredPrefix ([1,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[1,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_106 :
    filteredPrefix ([1,8,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_107 :
    filteredPrefix ([1,8,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_108 :
    filteredPrefix ([1,8,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_109 :
    filteredPrefix ([1,8,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_110 :
    filteredPrefix ([1,8,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_111 :
    filteredPrefix ([1,8,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_112 :
    filteredPrefix ([1,8,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_113 :
    filteredPrefix ([1,8,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_114 :
    filteredPrefix ([1,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_115 :
    filteredPrefix ([1,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_116 :
    filteredPrefix ([1,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,9,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_117 :
    filteredPrefix ([1,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_118 :
    filteredPrefix ([1,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_119 :
    filteredPrefix ([1,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[1,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_120 :
    filteredPrefix ([1,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,10,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_121 :
    filteredPrefix ([2,2,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,2,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_122 :
    filteredPrefix ([2,2,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,2,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_123 :
    filteredPrefix ([2,2,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,2,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_124 :
    filteredPrefix ([2,2,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,2,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_125 :
    filteredPrefix ([2,2,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,2,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_126 :
    filteredPrefix ([2,2,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,2,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_127 :
    filteredPrefix ([2,2,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,2,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_128 :
    filteredPrefix ([2,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [[2,3,3,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_129 :
    filteredPrefix ([2,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[2,3,6,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_130 :
    filteredPrefix ([2,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_131 :
    filteredPrefix ([2,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[2,3,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_132 :
    filteredPrefix ([2,5,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,5,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_133 :
    filteredPrefix ([2,5,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,5,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_134 :
    filteredPrefix ([2,5,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,5,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_135 :
    filteredPrefix ([2,5,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,5,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_136 :
    filteredPrefix ([2,5,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,5,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_137 :
    filteredPrefix ([2,5,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,5,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_138 :
    filteredPrefix ([2,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[2,6,6,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_139 :
    filteredPrefix ([2,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_140 :
    filteredPrefix ([2,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[2,6,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_141 :
    filteredPrefix ([2,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_142 :
    filteredPrefix ([2,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_143 :
    filteredPrefix ([2,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_144 :
    filteredPrefix ([2,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,9,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_145 :
    filteredPrefix ([2,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_146 :
    filteredPrefix ([2,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([2,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_147 :
    filteredPrefix ([2,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[2,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_148 :
    filteredPrefix ([2,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[2,10,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_149 :
    filteredPrefix ([3,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [[3,3,3,3,7,7,7,7],
[3,3,3,6,7,7,7,7],
[3,3,3,7,7,7,7,7],
[3,3,3,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_150 :
    filteredPrefix ([3,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[3,3,6,6,7,7,7,7],
[3,3,6,7,7,7,7,7],
[3,3,6,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_151 :
    filteredPrefix ([3,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[3,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_152 :
    filteredPrefix ([3,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[3,3,10,7,7,7,7,7],
[3,3,10,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_153 :
    filteredPrefix ([3,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[3,6,6,6,7,7,7,7],
[3,6,6,7,7,7,7,7],
[3,6,6,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_154 :
    filteredPrefix ([3,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[3,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_155 :
    filteredPrefix ([3,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[3,6,10,7,7,7,7,7],
[3,6,10,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_156 :
    filteredPrefix ([3,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[3,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_157 :
    filteredPrefix ([3,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[3,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_158 :
    filteredPrefix ([3,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[3,10,10,7,7,7,7,7],
[3,10,10,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_159 :
    filteredPrefix ([4,2,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_160 :
    filteredPrefix ([4,2,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_161 :
    filteredPrefix ([4,2,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_162 :
    filteredPrefix ([4,2,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_163 :
    filteredPrefix ([4,2,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_164 :
    filteredPrefix ([4,2,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_165 :
    filteredPrefix ([4,2,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,2,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_166 :
    filteredPrefix ([4,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,3,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_167 :
    filteredPrefix ([4,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,3,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_168 :
    filteredPrefix ([4,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[4,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_169 :
    filteredPrefix ([4,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,3,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_170 :
    filteredPrefix ([4,4,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_171 :
    filteredPrefix ([4,4,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_172 :
    filteredPrefix ([4,4,4] : List Kind) (orderKey (4 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,4] : List Kind)
    (orderKey (4 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_173 :
    filteredPrefix ([4,4,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_174 :
    filteredPrefix ([4,4,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_175 :
    filteredPrefix ([4,4,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_176 :
    filteredPrefix ([4,4,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_177 :
    filteredPrefix ([4,4,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_178 :
    filteredPrefix ([4,4,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,4,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_179 :
    filteredPrefix ([4,5,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,5,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_180 :
    filteredPrefix ([4,5,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,5,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_181 :
    filteredPrefix ([4,5,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,5,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_182 :
    filteredPrefix ([4,5,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,5,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_183 :
    filteredPrefix ([4,5,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,5,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_184 :
    filteredPrefix ([4,5,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,5,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_185 :
    filteredPrefix ([4,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,6,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_186 :
    filteredPrefix ([4,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[4,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_187 :
    filteredPrefix ([4,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,6,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_188 :
    filteredPrefix ([4,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[4,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_189 :
    filteredPrefix ([4,8,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_190 :
    filteredPrefix ([4,8,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_191 :
    filteredPrefix ([4,8,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_192 :
    filteredPrefix ([4,8,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_193 :
    filteredPrefix ([4,8,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_194 :
    filteredPrefix ([4,8,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_195 :
    filteredPrefix ([4,8,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_196 :
    filteredPrefix ([4,8,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,8,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_197 :
    filteredPrefix ([4,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_198 :
    filteredPrefix ([4,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_199 :
    filteredPrefix ([4,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,9,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_200 :
    filteredPrefix ([4,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_201 :
    filteredPrefix ([4,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_202 :
    filteredPrefix ([4,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[4,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_203 :
    filteredPrefix ([4,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([4,10,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_204 :
    filteredPrefix ([5,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [[5,3,3,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_205 :
    filteredPrefix ([5,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[5,3,6,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_206 :
    filteredPrefix ([5,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[5,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_207 :
    filteredPrefix ([5,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[5,3,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_208 :
    filteredPrefix ([5,5,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,5,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_209 :
    filteredPrefix ([5,5,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,5,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_210 :
    filteredPrefix ([5,5,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,5,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_211 :
    filteredPrefix ([5,5,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[5,5,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_212 :
    filteredPrefix ([5,5,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,5,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_213 :
    filteredPrefix ([5,5,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,5,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_214 :
    filteredPrefix ([5,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[5,6,6,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_215 :
    filteredPrefix ([5,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[5,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_216 :
    filteredPrefix ([5,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[5,6,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_217 :
    filteredPrefix ([5,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[5,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_218 :
    filteredPrefix ([5,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_219 :
    filteredPrefix ([5,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_220 :
    filteredPrefix ([5,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[5,9,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_221 :
    filteredPrefix ([5,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_222 :
    filteredPrefix ([5,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([5,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_223 :
    filteredPrefix ([5,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[5,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_224 :
    filteredPrefix ([5,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[5,10,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_225 :
    filteredPrefix ([6,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[6,6,6,6,7,7,7,7],
[6,6,6,7,7,7,7,7],
[6,6,6,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_226 :
    filteredPrefix ([6,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[6,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_227 :
    filteredPrefix ([6,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[6,6,10,7,7,7,7,7],
[6,6,10,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_228 :
    filteredPrefix ([6,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[6,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_229 :
    filteredPrefix ([6,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[6,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_230 :
    filteredPrefix ([6,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[6,10,10,7,7,7,7,7],
[6,10,10,10,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_231 :
    filteredPrefix ([7,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[7,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_232 :
    filteredPrefix ([8,2,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_233 :
    filteredPrefix ([8,2,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_234 :
    filteredPrefix ([8,2,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_235 :
    filteredPrefix ([8,2,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_236 :
    filteredPrefix ([8,2,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_237 :
    filteredPrefix ([8,2,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_238 :
    filteredPrefix ([8,2,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,2,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_239 :
    filteredPrefix ([8,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,3,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_240 :
    filteredPrefix ([8,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,3,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_241 :
    filteredPrefix ([8,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[8,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_242 :
    filteredPrefix ([8,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,3,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_243 :
    filteredPrefix ([8,5,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,5,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_244 :
    filteredPrefix ([8,5,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,5,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_245 :
    filteredPrefix ([8,5,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,5,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_246 :
    filteredPrefix ([8,5,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,5,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_247 :
    filteredPrefix ([8,5,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,5,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_248 :
    filteredPrefix ([8,5,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,5,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_249 :
    filteredPrefix ([8,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,6,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_250 :
    filteredPrefix ([8,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[8,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_251 :
    filteredPrefix ([8,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,6,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_252 :
    filteredPrefix ([8,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[8,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_253 :
    filteredPrefix ([8,8,2] : List Kind) (orderKey (2 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,2] : List Kind)
    (orderKey (2 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_254 :
    filteredPrefix ([8,8,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_255 :
    filteredPrefix ([8,8,5] : List Kind) (orderKey (5 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,5] : List Kind)
    (orderKey (5 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_256 :
    filteredPrefix ([8,8,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_257 :
    filteredPrefix ([8,8,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_258 :
    filteredPrefix ([8,8,8] : List Kind) (orderKey (8 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,8] : List Kind)
    (orderKey (8 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_259 :
    filteredPrefix ([8,8,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_260 :
    filteredPrefix ([8,8,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,8,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_261 :
    filteredPrefix ([8,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_262 :
    filteredPrefix ([8,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_263 :
    filteredPrefix ([8,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,9,7] : List Kind)
    (orderKey (7 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_264 :
    filteredPrefix ([8,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_265 :
    filteredPrefix ([8,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_266 :
    filteredPrefix ([8,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[8,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_267 :
    filteredPrefix ([8,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([8,10,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_268 :
    filteredPrefix ([9,3,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [[9,3,3,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_269 :
    filteredPrefix ([9,3,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[9,3,6,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_270 :
    filteredPrefix ([9,3,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[9,3,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_271 :
    filteredPrefix ([9,3,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[9,3,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_272 :
    filteredPrefix ([9,6,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [[9,6,6,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_273 :
    filteredPrefix ([9,6,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[9,6,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_274 :
    filteredPrefix ([9,6,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[9,6,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_275 :
    filteredPrefix ([9,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[9,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_276 :
    filteredPrefix ([9,9,3] : List Kind) (orderKey (3 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([9,9,3] : List Kind)
    (orderKey (3 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_277 :
    filteredPrefix ([9,9,6] : List Kind) (orderKey (6 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([9,9,6] : List Kind)
    (orderKey (6 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_278 :
    filteredPrefix ([9,9,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[9,9,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_279 :
    filteredPrefix ([9,9,9] : List Kind) (orderKey (9 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([9,9,9] : List Kind)
    (orderKey (9 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_280 :
    filteredPrefix ([9,9,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [] := by
  exact filteredPrefix_eq_nil_of_budget ([9,9,10] : List Kind)
    (orderKey (10 : Kind)) 5 (by decide +kernel)


private theorem type8_prefix_281 :
    filteredPrefix ([9,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[9,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_282 :
    filteredPrefix ([9,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[9,10,10,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_283 :
    filteredPrefix ([10,7,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[10,7,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_284 :
    filteredPrefix ([10,10,7] : List Kind) (orderKey (7 : Kind)) 5 =
      [[10,10,7,7,7,7,7,7]] := by decide +kernel


private theorem type8_prefix_285 :
    filteredPrefix ([10,10,10] : List Kind) (orderKey (10 : Kind)) 5 =
      [[10,10,10,7,7,7,7,7],
[10,10,10,10,7,7,7,7]] := by decide +kernel


theorem types8_eq : ThreeBoundRelaxedCoverage.activeTypes 8=types8 := by
  rw [activeTypes_eq_filteredPrefix]
  rw [show 8=5+3 from rfl, filteredPrefix_three_expanded]
  simp only [type8_prefix_000, type8_prefix_001, type8_prefix_002, type8_prefix_003, type8_prefix_004, type8_prefix_005, type8_prefix_006, type8_prefix_007, type8_prefix_008, type8_prefix_009, type8_prefix_010, type8_prefix_011, type8_prefix_012, type8_prefix_013, type8_prefix_014, type8_prefix_015, type8_prefix_016, type8_prefix_017, type8_prefix_018, type8_prefix_019, type8_prefix_020, type8_prefix_021, type8_prefix_022, type8_prefix_023, type8_prefix_024, type8_prefix_025, type8_prefix_026, type8_prefix_027, type8_prefix_028, type8_prefix_029, type8_prefix_030, type8_prefix_031, type8_prefix_032, type8_prefix_033, type8_prefix_034, type8_prefix_035, type8_prefix_036, type8_prefix_037, type8_prefix_038, type8_prefix_039, type8_prefix_040, type8_prefix_041, type8_prefix_042, type8_prefix_043, type8_prefix_044, type8_prefix_045, type8_prefix_046, type8_prefix_047, type8_prefix_048, type8_prefix_049, type8_prefix_050, type8_prefix_051, type8_prefix_052, type8_prefix_053, type8_prefix_054, type8_prefix_055, type8_prefix_056, type8_prefix_057, type8_prefix_058, type8_prefix_059, type8_prefix_060, type8_prefix_061, type8_prefix_062, type8_prefix_063, type8_prefix_064, type8_prefix_065, type8_prefix_066, type8_prefix_067, type8_prefix_068, type8_prefix_069, type8_prefix_070, type8_prefix_071, type8_prefix_072, type8_prefix_073, type8_prefix_074, type8_prefix_075, type8_prefix_076, type8_prefix_077, type8_prefix_078, type8_prefix_079, type8_prefix_080, type8_prefix_081, type8_prefix_082, type8_prefix_083, type8_prefix_084, type8_prefix_085, type8_prefix_086, type8_prefix_087, type8_prefix_088, type8_prefix_089, type8_prefix_090, type8_prefix_091, type8_prefix_092, type8_prefix_093, type8_prefix_094, type8_prefix_095, type8_prefix_096, type8_prefix_097, type8_prefix_098, type8_prefix_099, type8_prefix_100, type8_prefix_101, type8_prefix_102, type8_prefix_103, type8_prefix_104, type8_prefix_105, type8_prefix_106, type8_prefix_107, type8_prefix_108, type8_prefix_109, type8_prefix_110, type8_prefix_111, type8_prefix_112, type8_prefix_113, type8_prefix_114, type8_prefix_115, type8_prefix_116, type8_prefix_117, type8_prefix_118, type8_prefix_119, type8_prefix_120, type8_prefix_121, type8_prefix_122, type8_prefix_123, type8_prefix_124, type8_prefix_125, type8_prefix_126, type8_prefix_127, type8_prefix_128, type8_prefix_129, type8_prefix_130, type8_prefix_131, type8_prefix_132, type8_prefix_133, type8_prefix_134, type8_prefix_135, type8_prefix_136, type8_prefix_137, type8_prefix_138, type8_prefix_139, type8_prefix_140, type8_prefix_141, type8_prefix_142, type8_prefix_143, type8_prefix_144, type8_prefix_145, type8_prefix_146, type8_prefix_147, type8_prefix_148, type8_prefix_149, type8_prefix_150, type8_prefix_151, type8_prefix_152, type8_prefix_153, type8_prefix_154, type8_prefix_155, type8_prefix_156, type8_prefix_157, type8_prefix_158, type8_prefix_159, type8_prefix_160, type8_prefix_161, type8_prefix_162, type8_prefix_163, type8_prefix_164, type8_prefix_165, type8_prefix_166, type8_prefix_167, type8_prefix_168, type8_prefix_169, type8_prefix_170, type8_prefix_171, type8_prefix_172, type8_prefix_173, type8_prefix_174, type8_prefix_175, type8_prefix_176, type8_prefix_177, type8_prefix_178, type8_prefix_179, type8_prefix_180, type8_prefix_181, type8_prefix_182, type8_prefix_183, type8_prefix_184, type8_prefix_185, type8_prefix_186, type8_prefix_187, type8_prefix_188, type8_prefix_189, type8_prefix_190, type8_prefix_191, type8_prefix_192, type8_prefix_193, type8_prefix_194, type8_prefix_195, type8_prefix_196, type8_prefix_197, type8_prefix_198, type8_prefix_199, type8_prefix_200, type8_prefix_201, type8_prefix_202, type8_prefix_203, type8_prefix_204, type8_prefix_205, type8_prefix_206, type8_prefix_207, type8_prefix_208, type8_prefix_209, type8_prefix_210, type8_prefix_211, type8_prefix_212, type8_prefix_213, type8_prefix_214, type8_prefix_215, type8_prefix_216, type8_prefix_217, type8_prefix_218, type8_prefix_219, type8_prefix_220, type8_prefix_221, type8_prefix_222, type8_prefix_223, type8_prefix_224, type8_prefix_225, type8_prefix_226, type8_prefix_227, type8_prefix_228, type8_prefix_229, type8_prefix_230, type8_prefix_231, type8_prefix_232, type8_prefix_233, type8_prefix_234, type8_prefix_235, type8_prefix_236, type8_prefix_237, type8_prefix_238, type8_prefix_239, type8_prefix_240, type8_prefix_241, type8_prefix_242, type8_prefix_243, type8_prefix_244, type8_prefix_245, type8_prefix_246, type8_prefix_247, type8_prefix_248, type8_prefix_249, type8_prefix_250, type8_prefix_251, type8_prefix_252, type8_prefix_253, type8_prefix_254, type8_prefix_255, type8_prefix_256, type8_prefix_257, type8_prefix_258, type8_prefix_259, type8_prefix_260, type8_prefix_261, type8_prefix_262, type8_prefix_263, type8_prefix_264, type8_prefix_265, type8_prefix_266, type8_prefix_267, type8_prefix_268, type8_prefix_269, type8_prefix_270, type8_prefix_271, type8_prefix_272, type8_prefix_273, type8_prefix_274, type8_prefix_275, type8_prefix_276, type8_prefix_277, type8_prefix_278, type8_prefix_279, type8_prefix_280, type8_prefix_281, type8_prefix_282, type8_prefix_283, type8_prefix_284, type8_prefix_285] <;> rfl

end ThreeBoundEndpoint22Types


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
  (Sensitivity213981Formal.ThreeBoundRelaxedCoverage.activeTypes
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  Sensitivity213981Formal.ThreeBoundEndpoint22Types.types8 := @Sensitivity213981Formal.ThreeBoundEndpoint22Types.types8_eq
