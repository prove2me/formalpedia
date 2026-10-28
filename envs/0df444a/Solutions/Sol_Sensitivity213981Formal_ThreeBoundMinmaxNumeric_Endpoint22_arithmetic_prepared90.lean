-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_prepared90
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:11:12.382704+00:00
-- url     : https://prove2.me/submissions/ac9706a7-0397-4efc-93c9-e806b39b970b

import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData011
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData028
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData041
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData046
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData059
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData068
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData072
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData087
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData089
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData091
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData092
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch000
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch001
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch002
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch004
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch005
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch006
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch008
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch009
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch010
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch011
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch012
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch013
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch014
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch015
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch016
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch017
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch018
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch019
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch020
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch021
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared91
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankAnnotated_Tree_preparedCheck_of_dominance


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem coefficient_dominance90 : CoefficientLe 3 values90 values91 bound90 bound91 := by decide +kernel

theorem mask_dominance90 : MaskLe mask90 mask91 := by decide +kernel

theorem arithmetic_prepared90 : annotated.preparedCheck mask90 3 (prepared keyCodes.get convertedValues 3) values90 bound90=true :=
  Tree.preparedCheck_of_dominance mask90 mask91 mask_dominance90 3
    (prepared keyCodes.get convertedValues 3) values90 values91 bound90 bound91
    (by decide) coefficient_dominance90 annotated arithmetic_prepared91
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.mask90
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
      Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values90
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound90
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated)
  Bool.true := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.arithmetic_prepared90
