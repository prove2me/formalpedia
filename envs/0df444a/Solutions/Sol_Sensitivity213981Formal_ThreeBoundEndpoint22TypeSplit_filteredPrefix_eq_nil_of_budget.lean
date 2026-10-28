-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_eq_nil_of_budget
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:03:13.972598+00:00
-- url     : https://prove2.me/submissions/962a609e-bc61-488f-81b1-73747e47fa25

import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
import Definitions.Def_Sensitivity213981Formal_HighTypeCore
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedCoverage_typeLists_length


namespace Sensitivity213981Formal
section
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes

















theorem budget_le (q : ℕ) (k : Kind q) : budget q k ≤  q+1 := by
  have hk := k.isLt
  unfold budget
  split_ifs <;> omega





end ThreeBoundHighTypes




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Sound early rejection of a type-list pref. -/

set_option autoImplicit false
namespace ThreeBoundEndpoint22TypeSplit
open ThreeBoundQ3






theorem budget_sum_le_four (ts : List Kind) :
    (ts.map budget).sum ≤  4*ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      have ht : budget t ≤  4 := ThreeBoundHighTypes.budget_le 3 t
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega

theorem filteredPrefix_eq_nil_of_budget
    (pref : List Kind) (lo n : ℕ)
    (hbad : ¬ ((pref.length+n)*(pref.length+n-1)/2 ≤ 
      (pref.map budget).sum+4*n)) :
    filteredPrefix pref lo n = [] := by
  unfold filteredPrefix
  apply List.filter_eq_nil_iff.mpr
  intro ts hts
  obtain ⟨suffix,hsuffix,rfl⟩ := List.mem_map.mp hts
  intro hallowed
  have ha : allowedTypes (pref ++ suffix) := of_decide_eq_true hallowed
  have hslen : suffix.length=n :=
    ThreeBoundRelaxedCoverage.typeLists_length lo n suffix hsuffix
  have hb : (pref ++ suffix).length*((pref ++ suffix).length-1)/2 ≤ 
      ((pref ++ suffix).map budget).sum := by
    simpa only [List.take_length] using
      ha.1 ⟨(pref ++ suffix).length,by omega⟩
  have htotal : (pref.length+n)*(pref.length+n-1)/2 ≤ 
      (pref.map budget).sum+(suffix.map budget).sum := by
    simpa only [List.length_append,List.map_append,List.sum_append,hslen] using hb
  have hsum : (suffix.map budget).sum ≤  4*n := by
    simpa only [hslen] using budget_sum_le_four suffix
  exact hbad (htotal.trans (Nat.add_le_add_left hsum _))

end ThreeBoundEndpoint22TypeSplit




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (pref : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (lo n : Nat)
  (hbad :
    Not
      (@LE.le.{0} Nat instLENat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind pref) n)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind pref) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
            (@List.map.{0, 0}
              (Sensitivity213981Formal.ThreeBoundHighTypes.Kind
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              Nat Sensitivity213981Formal.ThreeBoundQ3.budget pref))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n)))),
  @Eq.{1} (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
    (Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix pref lo n)
    (@List.nil.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)) := @Sensitivity213981Formal.ThreeBoundEndpoint22TypeSplit.filteredPrefix_eq_nil_of_budget
