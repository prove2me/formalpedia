-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_three
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:32:15.781103+00:00
-- url     : https://prove2.me/submissions/ecae2bc4-8671-491e-8fbc-bfcb102ba778

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





theorem filteredPrefix_step (pref : List Kind) (lo n : ℕ) :
    filteredPrefix pref lo (n+1) =
      (List.finRange 11).flatMap (fun t =>
        if lo ≤  orderKey t then filteredPrefix (pref ++ [t]) (orderKey t) n else []) := by
  simp only [filteredPrefix, typeLists, List.map_flatMap, List.filter_flatMap]
  apply congrArg (fun f : Kind → List (List Kind) => (List.finRange 11).flatMap f)
  funext t
  by_cases h : lo ≤  orderKey t
  · simp only [if_pos h, List.map_map, Function.comp_def,
      List.append_assoc, List.singleton_append]
  · simp only [if_neg h, List.map_nil, List.filter_nil]

theorem filteredPrefix_three (pref : List Kind) (lo n : ℕ) :
    filteredPrefix pref lo (n+3) =
      (List.finRange 11).flatMap (fun a =>
        if lo ≤  orderKey a then
          (List.finRange 11).flatMap (fun b =>
            if orderKey a ≤  orderKey b then
              (List.finRange 11).flatMap (fun c =>
                if orderKey b ≤  orderKey c then
                  filteredPrefix (pref ++ [a,b,c]) (orderKey c) n
                else [])
            else [])
        else []) := by
  rw [filteredPrefix_step]
  apply congrArg (fun f : Kind → List (List Kind) => (List.finRange 11).flatMap f)
  funext a
  split_ifs with ha
  · rw [filteredPrefix_step]
    apply congrArg (fun f : Kind → List (List Kind) => (List.finRange 11).flatMap f)
    funext b
    split_ifs with hb
    · rw [filteredPrefix_step]
      simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
    · rfl
  · rfl

end ThreeBoundEndpoint22TypeSplit




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (pref : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (lo n : Nat),
  @Eq.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
    (Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix pref lo
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@List.flatMap.{0, 0} Sensitivity213981Formal.ThreeBoundQ3.Kind (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
      (fun (a : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
        @ite.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
          (@LE.le.{0} Nat instLENat lo (Sensitivity213981Formal.ThreeBoundQ3.orderKey a))
          (Nat.decLe lo (Sensitivity213981Formal.ThreeBoundQ3.orderKey a))
          (@List.flatMap.{0, 0} Sensitivity213981Formal.ThreeBoundQ3.Kind
            (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
            (fun (b : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
              @ite.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
                (@LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                  (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
                (Nat.decLe (Sensitivity213981Formal.ThreeBoundQ3.orderKey a)
                  (Sensitivity213981Formal.ThreeBoundQ3.orderKey b))
                (@List.flatMap.{0, 0} Sensitivity213981Formal.ThreeBoundQ3.Kind
                  (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                  (fun (c : Sensitivity213981Formal.ThreeBoundQ3.Kind) =>
                    @ite.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
                      (@LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundQ3.orderKey b)
                        (Sensitivity213981Formal.ThreeBoundQ3.orderKey c))
                      (Nat.decLe (Sensitivity213981Formal.ThreeBoundQ3.orderKey b)
                        (Sensitivity213981Formal.ThreeBoundQ3.orderKey c))
                      (Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix
                        (@HAppend.hAppend.{0, 0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                          (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                          (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                          (@instHAppendOfAppend.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
                            (@List.instAppend.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
                          pref
                          (@List.cons.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind a
                            (@List.cons.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind b
                              (@List.cons.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind c
                                (@List.nil.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))))
                        (Sensitivity213981Formal.ThreeBoundQ3.orderKey c) n)
                      (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))
                  (List.finRange (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))
            (List.finRange (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
          (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)))
      (List.finRange (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))) := @Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_three
