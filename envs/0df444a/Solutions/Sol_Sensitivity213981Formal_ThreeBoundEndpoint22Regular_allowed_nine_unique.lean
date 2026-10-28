-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Regular.allowed_nine_unique
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:29.895201+00:00
-- url     : https://prove2.me/submissions/8b8d6b0d-6006-4b78-afd4-e89f172dc789

import Definitions.Def_Sensitivity213981Formal_Endpoint22RegularRecord
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


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
/- The saturated nine-guard case has a single exact record, independently
of its orientation.  This replaces exhaustive reductions of regular tournaments. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

namespace ThreeBoundEndpoint22Regular
open ThreeBoundQ3 ThreeBoundQ3RecordFields ThreeBoundSaturated














theorem budget_four_iff (k : Kind) : budget k=4 ↔ k=7 := by
  fin_cases k <;> decide

/-- The total budget at nine vertices forces every kind to be the top guard
kind, before any orientation generation is performed. -/
theorem allowed_nine_unique (ts : List Kind) (hlen : ts.length=9) (ht : allowedTypes ts) :
    ts=allG3 := by
  have hsum : 36 ≤  (ts.map budget).sum := by
    have hh := ht.1 ⟨ts.length,by omega⟩
    change ts.length*(ts.length-1)/2 ≤  ((ts.take ts.length).map budget).sum at hh
    rw [List.take_length,hlen] at hh
    exact hh
  have hmap : List.ofFn (fun v : Fin ts.length => budget (ts.get v))=ts.map budget := by
    have hh := List.map_ofFn (f:=ts.get) (g:=budget)
    rw [List.ofFn_get] at hh
    exact hh.symm
  have he := congrArg List.sum hmap
  rw [List.sum_ofFn] at he
  have htot : (∑ _v : Fin ts.length, (4 : ℕ))=36 := by simp [hlen]
  have hbudget : ∀ v : Fin ts.length, budget (ts.get v)=4 := by
    intro v
    have hle : budget (ts.get v) ≤  4 := ThreeBoundHighTypes.budget_le 3 (ts.get v)
    apply le_antisymm hle
    by_contra hn
    have hlt : budget (ts.get v)< 4 := by omega
    have hh := Finset.sum_lt_sum
      (fun w (_ : w ∈ (Finset.univ : Finset (Fin ts.length))) => ThreeBoundHighTypes.budget_le 3 (ts.get w))
      ⟨v,Finset.mem_univ v,hlt⟩
    change (∑ w : Fin ts.length, budget (ts.get w)) <  ∑ _w : Fin ts.length, (4 : ℕ) at hh
    rw [he,htot] at hh
    omega
  apply List.eq_replicate_iff.mpr
  refine ⟨hlen,?_⟩
  intro k hk
  obtain ⟨v,hv⟩ := List.mem_iff_get.mp hk
  rw [← hv]
  exact (budget_four_iff _).1 (hbudget v)



end ThreeBoundEndpoint22Regular






end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (hlen :
    @Eq.{1} Nat (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts)
      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
  (ht : Sensitivity213981Formal.ThreeBoundQ3.allowedTypes ts),
  @Eq.{1} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) ts
    Sensitivity213981Formal.ThreeBoundEndpoint22Regular.allG3 := @Sensitivity213981Formal.ThreeBoundEndpoint22Regular.allowed_nine_unique
