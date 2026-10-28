-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Records.all_prepared
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:29.279848+00:00
-- url     : https://prove2.me/submissions/9a041e4c-c312-483b-bba3-ca24accea26a

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22SummaryData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_annotated_statics_checked
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_converted_correct
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_Tree_allPrepared_of_statics


namespace Sensitivity213981Formal
section

set_option autoImplicit false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankCached ThreeBoundRankAnnotated

theorem all_prepared (q : ℕ) (hq : q≤ 3) :
    annotated.AllPrepared ThreeBoundOrdinary5591.numericCaps 14 q
      (prepared keyCodes.get convertedValues q) :=
  Tree.allPrepared_of_statics ThreeBoundOrdinary5591.numericCaps 14 keyCodes.get convertedValues
    keyCount q hq converted_correct annotated annotated_statics_checked
end ThreeBoundEndpoint22Records


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (q : Nat) (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.AllPrepared
    Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) q
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
      Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues q)
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated := @Sensitivity213981Formal.ThreeBoundEndpoint22Records.all_prepared
