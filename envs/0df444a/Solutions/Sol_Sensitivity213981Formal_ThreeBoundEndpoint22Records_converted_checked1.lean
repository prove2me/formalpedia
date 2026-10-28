-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Records.converted_checked1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:55:49.754903+00:00
-- url     : https://prove2.me/submissions/33b88ce5-fb68-43d3-9133-02fd7dbd4181

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22SummaryData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile






























theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤  k ∧ k <  b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩











end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile

variable {n : ℕ}

































theorem checkInterval_sound (p : ℕ → Bool) (a b : ℕ)
    (h : checkInterval p a b = true) (k : ℕ) (ha : a≤ k) (hb : k< b) : p k=true :=
  List.all_eq_true.mp h k (mem_interval.mpr ⟨ha,hb⟩)

theorem checkInterval_join (p : ℕ → Bool) (a b c : ℕ)
    (hab : checkInterval p a b=true) (hbc : checkInterval p b c=true) :
    checkInterval p a c=true := by
  apply List.all_eq_true.mpr
  intro k hk
  obtain ⟨ha,hc⟩ := mem_interval.mp hk
  by_cases hb : k< b
  · exact checkInterval_sound p a b hab k ha hb
  · exact checkInterval_sound p b c hbc k (by omega) hc









end ThreeBoundNumeric.ClosureCertificate



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundNumeric.ClosureCertificate
private theorem part0 : checkInterval summaryCheckAt 128 160=true:=by decide +kernel
private theorem part1 : checkInterval summaryCheckAt 160 192=true:=by decide +kernel
private theorem part2 : checkInterval summaryCheckAt 192 224=true:=by decide +kernel
private theorem part3 : checkInterval summaryCheckAt 224 256=true:=by decide +kernel
theorem converted_checked1 : checkInterval summaryCheckAt 128 256=true:=
  (checkInterval_join summaryCheckAt 128 192 256 (checkInterval_join summaryCheckAt 128 160 192 part0 part1) (checkInterval_join summaryCheckAt 192 224 256 part2 part3))
end ThreeBoundEndpoint22Records


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.checkInterval
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.summaryCheckAt
    (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))
    (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Records.converted_checked1
