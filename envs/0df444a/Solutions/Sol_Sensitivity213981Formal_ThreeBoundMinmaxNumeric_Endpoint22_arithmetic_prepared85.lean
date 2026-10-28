-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_prepared85
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:46:49.551187+00:00
-- url     : https://prove2.me/submissions/944f7aa1-f99a-4df2-a17d-b2f0645b14a2

import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared82
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_Tree_preparedCheck_of_dominance


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem coefficient_dominance85 : CoefficientLe 0 values85 values82 bound85 bound82 := by decide +kernel

theorem mask_dominance85 : MaskLe mask85 mask82 := by decide +kernel

theorem arithmetic_prepared85 : annotated.preparedCheck mask85 0 (prepared keyCodes.get convertedValues 0) values85 bound85=true :=
  Tree.preparedCheck_of_dominance mask85 mask82 mask_dominance85 0
    (prepared keyCodes.get convertedValues 0) values85 values82 bound85 bound82
    (by decide) coefficient_dominance85 annotated arithmetic_prepared82
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.mask85
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
      Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values85
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound85
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_prepared85
