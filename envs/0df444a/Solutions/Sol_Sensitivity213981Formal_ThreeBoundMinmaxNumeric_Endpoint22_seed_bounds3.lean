-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.seed_bounds3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:06:13.381052+00:00
-- url     : https://prove2.me/submissions/fd2660fc-18a0-4ff7-968a-dfff98720772

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22CodeRecord
import Definitions.Def_Sensitivity213981Formal_Endpoint22CostValues
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22HybridTransfer
import Definitions.Def_Sensitivity213981Formal_Endpoint22NibbleMask
import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericData
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22SeedCover3
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22SummaryData
import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankCachedEvaluator
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
import Definitions.Def_Sensitivity213981Formal_RankFusedCoefficients
import Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch000
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch001
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch002
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch003
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch004
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch005
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch006
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch007
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
import Init.Data.Nat.Bitwise.Lemmas
import Lean
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_all_prepared
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared158
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared159
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared161
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared162
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared164
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared165
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared167
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared169
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared171
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared172
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared173
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared174
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared176
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared177
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared178
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared179
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared180
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared182
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared183
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared185
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared186
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared187
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared188
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared189
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared190
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared191
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared194
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared195
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_arithmetic_prepared200
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_10_10
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_10_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_10_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_11_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_11_12
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_11_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_12_12
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_12_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_13_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_13_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_14_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_15_15
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_16_16
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_17_17
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_18_18
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_19_19
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_1_2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_20_20
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_21_21
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_2_2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_2_3
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_3_3
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_3_4
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_3_5
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_4_4
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_4_6
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_4_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_5_16
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_5_5
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_5_7
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_5_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_6_6
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_7_7
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_7_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_8_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bound_transfer_3_9_9
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_10_10
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_10_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_10_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_11_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_11_12
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_11_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_12_12
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_12_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_13_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_13_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_14_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_15_15
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_16_16
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_17_17
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_18_18
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_19_19
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_1_2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_20_20
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_21_21
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_2_2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_2_3
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_3_3
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_3_4
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_3_5
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_4_4
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_4_6
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_4_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_5_16
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_5_5
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_5_7
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_5_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_6_6
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_7_7
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_7_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_8_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_coefficients_correct_3_9_9
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_10_10
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_10_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_10_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_11_11
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_11_12
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_11_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_12_12
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_12_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_13_13
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_13_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_14_14
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_15_15
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_16_16
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_17_17
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_18_18
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_19_19
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_1_2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_20_20
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_21_21
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_2_2
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_2_3
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_3_3
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_3_4
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_3_5
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_4_4
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_4_6
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_4_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_5_16
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_5_5
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_5_7
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_5_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_6_6
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_7_7
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_7_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_8_8
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_mask_correct_3_9_9
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankCached_rankA_le_of_bounds


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile
























theorem Expr.eval_sum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.sum es).eval v = (es.map (fun e=>e.eval v)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.sum,List.foldr_cons,Expr.eval,List.map_cons,
      List.sum_cons] using congrArg (fun z=>e.eval v+z) ih

















end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Symbolic transcription of graded2_union_recurrence.py, with the ordinary
q=1, three-positive cap corrected to marked[6]+2, the established general
bound. This correction changes no coordinate of the first endpoint's four
numerical phases, because every ordinary q=1 fallback there is absent.
The formulas are homogeneous natural arithmetic expressions. This module
defines the numeric raw transfer; its semantic raw-A/M/P/D obligations are
separate theorems about the actual Boolean parent. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile








@[simp] theorem eval_add {n : ℕ} (v : Profile n) (a b : Expr n) :
    (a+b).eval v = a.eval v+b.eval v := rfl

@[simp] theorem eval_mul {n : ℕ} (v : Profile n) (k : ℕ) (a : Expr n) :
    (k*a).eval v = k*a.eval v := rfl







































































end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact coefficient caching and filtered-tree bounds for the q3 rank transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps Expr aExpr bExpr recordOfList eval_add eval_mul maximum )
open ThreeBoundFullProfile ThreeBoundRankNumeric
open scoped BigOperators



















theorem recordAllowed_factor (n : ℕ) (caps : Caps) (a c : Entry) (mask : Array Bool)
    (hm : MaskOK n a c mask) (r : Record) :
    recordAllowed n caps a c r = (maskAllowed mask r && staticAllowed caps c.tolerance r) := by
  have hget : ∀ k : Fin 11, mask.getD k.val false=possible n a c k := hm
  simp only [recordAllowed,maskAllowed,staticAllowed,hget]





theorem headSum_eq (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues)
    (hc : CostOK n v a c values) (r : Record) :
    headSum values r=(highExpr n a c r).eval v := by
  have h0 (k : Fin 11) : values.heads.getD (3*k.val) 0=(rankCost n a c k 0).eval v := by
    simpa only [Fin.val_zero,Nat.add_zero] using hc.1 k 0
  have h1 (k : Fin 11) : values.heads.getD (3*k.val+1) 0=(rankCost n a c k 1).eval v := hc.1 k 1
  have h2 (k : Fin 11) : values.heads.getD (3*k.val+2) 0=(rankCost n a c k 2).eval v := hc.1 k 2
  simp only [headSum,highExpr,Expr.eval_sum,List.map_ofFn,Function.comp_def,eval_add,eval_mul,h0,h1,h2]

theorem cachedRecordCost_eq (n : ℕ) (v : Profile n) (caps : Caps) (perfect : ℕ)
    (a c : Entry) (values : CostValues) (hc : CostOK n v a c values) (r : Record) (e : ℕ) :
    cachedRecordCost caps perfect c.tolerance values r e=(recordCost n caps perfect a c r e).eval v := by
  have hn : ((List.range (c.tolerance+1)).map fun k =>
      negativeCount caps perfect c.tolerance r e k*values.negative.getD k 0).sum =
      (negativeExpr n caps perfect c r e).eval v := by
    simp only [negativeExpr,Expr.eval_sum,List.map_map,Function.comp_def,eval_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [hc.2.2.2 ⟨k,List.mem_range.mp hk⟩]
  simp only [cachedRecordCost,recordCost,eval_add,eval_mul,hc.2.1,hc.2.2.1,hn,headSum_eq n v a c values hc]













theorem preparedCost_eq (caps : Caps) (perfect q : ℕ) (p : PreparedValues)
    (values : CostValues) (r : Record) (hp : PreparedOK caps perfect q r p)
    (hf : p.feasible=true) (e : ℕ) (he : e≤ r 11) :
    preparedCost q p values r e=cachedRecordCost caps perfect q values r e := by
  unfold preparedCost cachedRecordCost
  congr 1
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [hp.2 hf ⟨e,by omega⟩ ⟨k,List.mem_range.mp hk⟩]



theorem record_bound_of_prepared (n : ℕ) (v : Profile n) (caps : Caps) (perfect : ℕ)
    (a c : Entry) (mask : Array Bool) (hm : MaskOK n a c mask)
    (p : PreparedValues) (values : CostValues) (bound : ℕ) (xs : List ℕ)
    (hp : PreparedOK caps perfect c.tolerance (recordOfList xs) p)
    (hc : CostOK n v a c values)
    (hcheck : preparedRecordCheck c.tolerance p values bound xs=true)
    (ha : recordAllowed n caps a c (recordOfList xs)=true)
    (e : ℕ) (he : e≤ recordOfList xs 11) :
    (recordCost n caps perfect a c (recordOfList xs) e).eval v≤ bound := by
  rw [recordAllowed_factor n caps a c mask hm,← hp.1] at ha
  have hap : maskAllowed mask (recordOfList xs)=true ∧ p.feasible=true := by
    simpa only [Bool.and_eq_true] using ha
  have hf : p.feasible=true := hap.2
  have hh : preparedCost c.tolerance p values (recordOfList xs) e≤ bound := by
    rw [preparedRecordCheck,if_pos hf] at hcheck
    exact of_decide_eq_true (List.all_eq_true.mp hcheck e (List.mem_range.mpr (by omega)))
  rw [preparedCost_eq caps perfect c.tolerance p values (recordOfList xs) hp hf e he,
    cachedRecordCost_eq n v caps perfect a c values hc] at hh
  exact hh











end ThreeBoundRankCached




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Direct field access to the lossless hexadecimal row encoding. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Records
open ThreeBoundNumeric (recordOfList)
open ThreeBoundRankNumeric



theorem decodeRow_getD (n x k : ℕ) :
    (decodeRow n x).getD k 0=if k< n then decodeDigit (x/(16^k)) else 0 := by
  induction n generalizing x k with
  | zero => simp [decodeRow,List.getD]
  | succ n ih =>
      cases k with
      | zero => simp [decodeRow,decodeDigit,List.getD_cons_zero]
      | succ k =>
          simp only [decodeRow,List.getD_cons_succ,ih,Nat.succ_lt_succ_iff]
          congr 1
          rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 16 (16^k)]



theorem codeRecord_eq (code : ℕ) : recordOfList (decodeRow 41 code)=codeRecord code := by
  funext k
  exact decodeRow_getD 41 code k

theorem decodeDigit_pos (x : ℕ) : 0< decodeDigit x ↔ 0< x%16 := by
  unfold decodeDigit
  split_ifs with h
  · simp [h]
  · rfl










end ThreeBoundEndpoint22Records


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Packed masks detect nonzero hexadecimal fields without decoding each field. -/


set_option autoImplicit false
set_option maxHeartbeats 400000

namespace ThreeBoundEndpoint22Records



theorem nibble_bit_pos (code k r : ℕ) (hr : r <  4)
    (hb : code.testBit (4*k+r) = true) : 0 <  (code/(16^k))%16 := by
  have hp : (16:ℕ)^k = 2^(4*k) := by
    calc
      (16:ℕ)^k = ((2:ℕ)^4)^k := by norm_num
      _ = 2^(4*k) := (pow_mul 2 4 k).symm
  have hd : (code/(16^k)).testBit r = true := by
    rw [hp, Nat.testBit_div_two_pow, Nat.add_comm r (4*k)]
    exact hb
  have hm : ((code/(16^k))%16).testBit r = true := by
    change ((code/(16^k))%2^4).testBit r = true
    simp only [Nat.testBit_mod_two_pow, hr, decide_true, Bool.true_and, hd]
  by_contra hn
  have hz : (code/(16^k))%16 = 0 := by omega
  rw [hz, Nat.zero_testBit] at hm
  contradiction

/-- A low-position bit in the spread certifies that its hexadecimal digit is nonzero. -/
theorem nibbleSpread_testBit_pos (code k : ℕ)
    (h : (nibbleSpread code).testBit (4*k) = true) :
    0 <  (code/(16^k))%16 := by
  simp only [nibbleSpread, Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
  rcases h with ((h|h)|h)|h
  · exact nibble_bit_pos code k 0 (by decide) (by simpa only [Nat.add_zero] using h)
  · exact nibble_bit_pos code k 1 (by decide) (by simpa only [Nat.add_comm] using h)
  · exact nibble_bit_pos code k 2 (by decide) (by simpa only [Nat.add_comm] using h)
  · exact nibble_bit_pos code k 3 (by decide) (by simpa only [Nat.add_comm] using h)

end ThreeBoundEndpoint22Records


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Certified common-kind masks skip whole impossible record subtrees. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace ThreeBoundRankAnnotated
open ThreeBoundNumeric (Caps recordOfList)
open ThreeBoundRankNumeric ThreeBoundRankCached ThreeBoundFullProfile
open ThreeBoundEndpoint22Records

theorem and_true {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h









theorem packedMaskCheck_sound (bits code : ℕ) (h : packedMaskCheck bits code=true)
    (k : Fin 11) (hk : bits.testBit (4*k.val)=true) : 0< codeRecord code k.val := by
  have he:=congrArg (fun x:ℕ=>x.testBit (4*k.val)) (of_decide_eq_true h)
  have hb:(nibbleSpread code).testBit (4*k.val)=true:=by
    simpa only [Nat.testBit_and,hk,Bool.true_and] using he
  unfold codeRecord
  rw [if_pos (by omega : k.val< 41)]
  exact (decodeDigit_pos _).mpr (nibbleSpread_testBit_pos code k.val hb)



theorem Tree.mask_sound (t : Tree) (h : t.checkMasks=true) (row : List ℕ)
    (hr : row∈t.erase.elements) (k : Fin 11) (hk : t.mask.testBit (4*k.val)=true) :
    0< recordOfList row k.val := by
  induction t with
  | leaf bits key code =>
      have he : row=decodeRow 41 code := List.mem_singleton.mp hr
      rw [he,codeRecord_eq]
      exact packedMaskCheck_sound bits code h k hk
  | branch bits pivot left right hl hr' =>
      change bits.testBit (4*k.val)=true at hk
      obtain ⟨hvalid,hmask⟩ := and_true h
      obtain ⟨hleft,hright⟩ := and_true hvalid
      have he : bits &&& left.mask=bits ∧ bits &&& right.mask=bits:=of_decide_eq_true hmask
      have hml:left.mask.testBit (4*k.val)=true:=by
        have hh:=congrArg (fun x:ℕ=>x.testBit (4*k.val)) he.1
        simpa only [Nat.testBit_and,hk,Bool.true_and] using hh
      have hmr:right.mask.testBit (4*k.val)=true:=by
        have hh:=congrArg (fun x:ℕ=>x.testBit (4*k.val)) he.2
        simpa only [Nat.testBit_and,hk,Bool.true_and] using hh
      rcases List.mem_append.mp hr with hr | hr
      · exact hl hleft hr hml
      · exact hr' hright hr hmr



theorem not_blocked_of_allowed (t : Tree) (h : t.checkMasks=true)
    (row : List ℕ) (hr : row∈t.erase.elements) (mask : Array Bool)
    (ha : maskAllowed mask (recordOfList row)=true) : blocked mask t.mask=false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  obtain ⟨k,hk,hbits⟩ := List.any_eq_true.mp hb
  obtain ⟨hbit,hno⟩ := and_true hbits
  have hp := t.mask_sound h row hr k hbit
  have hm := of_decide_eq_true (List.all_eq_true.mp ha k (List.mem_finRange k))
  have hn : mask.getD k.val false=false := by
    cases he : mask.getD k.val false with
    | false => rfl
    | true => simp only [he,Bool.not_true,Bool.false_eq_true] at hno
  rcases hm with hz | hy
  · omega
  · simp only [hn,Bool.false_eq_true] at hy





theorem codePreparedCheck_eq (q : ℕ) (p : PreparedValues) (values : CostValues)
    (bound code : ℕ) : codePreparedCheck q p values bound code=
      preparedRecordCheck q p values bound (decodeRow 41 code) := by
  simp only [codePreparedCheck,preparedRecordCheck,codeRecord_eq]



theorem Tree.preparedCheck_sound (n : ℕ) (v : Profile n) (caps : Caps) (perfect : ℕ)
    (a c : Entry) (mask : Array Bool) (hm : MaskOK n a c mask)
    (pre : ℕ → PreparedValues) (values : CostValues) (bound : ℕ)
    (hc : CostOK n v a c values) (t : Tree) (ht : t.checkMasks=true)
    (hp : t.AllPrepared caps perfect c.tolerance pre)
    (hcheck : t.preparedCheck mask c.tolerance pre values bound=true)
    (row : List ℕ) (hr : row∈t.erase.elements)
    (ha : recordAllowed n caps a c (recordOfList row)=true)
    (e : ℕ) (he : e≤ recordOfList row 11) :
    (recordCost n caps perfect a c (recordOfList row) e).eval v≤ bound := by
  have hallow : maskAllowed mask (recordOfList row)=true := by
    rw [recordAllowed_factor n caps a c mask hm] at ha
    exact (and_true ha).1
  induction t with
  | leaf bits key code =>
      have heq : row=decodeRow 41 code := List.mem_singleton.mp hr
      have hno := not_blocked_of_allowed (.leaf bits key code) ht row hr mask hallow
      simp only [Tree.preparedCheck,hno,Bool.false_eq_true,if_false,codePreparedCheck_eq] at hcheck
      subst row
      apply record_bound_of_prepared n v caps perfect a c mask hm (pre key) values bound (decodeRow 41 code) _ hc hcheck ha e he
      simpa only [Tree.AllPrepared,codeRecord_eq] using hp
  | branch bits pivot left right hl hr' =>
      have hno := not_blocked_of_allowed (.branch bits pivot left right) ht row hr mask hallow
      simp only [Tree.preparedCheck,hno,Bool.false_eq_true,if_false] at hcheck
      obtain ⟨hleft,hright⟩ := and_true hcheck
      obtain ⟨hvalid,_⟩ := and_true ht
      obtain ⟨hvleft,hvright⟩ := and_true hvalid
      rcases List.mem_append.mp hr with hr | hr
      · exact hl hvleft hp.1 hleft hr
      · exact hr' hvright hp.2 hright hr

theorem rawA_le_of_annotated (n : ℕ) (v : Profile n) (caps : Caps) (perfect : ℕ)
    (a c : Entry) (mask : Array Bool) (hm : MaskOK n a c mask)
    (pre : ℕ → PreparedValues) (values : CostValues) (bound : ℕ)
    (hc : CostOK n v a c values) (t : Tree) (ht : t.checkMasks=true)
    (hp : t.AllPrepared caps perfect c.tolerance pre) (hq : c.tolerance≤ 3)
    (hcheck : t.preparedCheck mask c.tolerance pre values bound=true) :
    (rawAExpr n caps perfect t.erase.elements a c).eval v≤ bound := by
  rw [rawAExpr,if_neg (by omega : ¬4≤ c.tolerance)]
  apply rankA_le_of_bounds
  exact fun row hr ha e he=>t.preparedCheck_sound n v caps perfect a c mask hm pre values bound hc ht hp hcheck row hr ha e he







end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased0 : annotated0.erase=subtree0:=by rfl

theorem masks_checked0 : annotated0.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased1 : annotated1.erase=subtree1:=by rfl

theorem masks_checked1 : annotated1.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased2 : annotated2.erase=subtree2:=by rfl

theorem masks_checked2 : annotated2.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased3 : annotated3.erase=subtree3:=by rfl

theorem masks_checked3 : annotated3.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased4 : annotated4.erase=subtree4:=by rfl

theorem masks_checked4 : annotated4.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased5 : annotated5.erase=subtree5:=by rfl

theorem masks_checked5 : annotated5.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased6 : annotated6.erase=subtree6:=by rfl

theorem masks_checked6 : annotated6.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased7 : annotated7.erase=subtree7:=by rfl

theorem masks_checked7 : annotated7.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased8 : annotated8.erase=subtree8:=by rfl

theorem masks_checked8 : annotated8.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased9 : annotated9.erase=subtree9:=by rfl

theorem masks_checked9 : annotated9.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased10 : annotated10.erase=subtree10:=by rfl

theorem masks_checked10 : annotated10.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased11 : annotated11.erase=subtree11:=by rfl

theorem masks_checked11 : annotated11.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased12 : annotated12.erase=subtree12:=by rfl

theorem masks_checked12 : annotated12.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased13 : annotated13.erase=subtree13:=by rfl

theorem masks_checked13 : annotated13.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased14 : annotated14.erase=subtree14:=by rfl

theorem masks_checked14 : annotated14.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased15 : annotated15.erase=subtree15:=by rfl

theorem masks_checked15 : annotated15.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased16 : annotated16.erase=subtree16:=by rfl

theorem masks_checked16 : annotated16.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased17 : annotated17.erase=subtree17:=by rfl

theorem masks_checked17 : annotated17.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased18 : annotated18.erase=subtree18:=by rfl

theorem masks_checked18 : annotated18.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased19 : annotated19.erase=subtree19:=by rfl

theorem masks_checked19 : annotated19.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased20 : annotated20.erase=subtree20:=by rfl

theorem masks_checked20 : annotated20.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased21 : annotated21.erase=subtree21:=by rfl

theorem masks_checked21 : annotated21.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased22 : annotated22.erase=subtree22:=by rfl

theorem masks_checked22 : annotated22.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased23 : annotated23.erase=subtree23:=by rfl

theorem masks_checked23 : annotated23.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased24 : annotated24.erase=subtree24:=by rfl

theorem masks_checked24 : annotated24.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased25 : annotated25.erase=subtree25:=by rfl

theorem masks_checked25 : annotated25.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased26 : annotated26.erase=subtree26:=by rfl

theorem masks_checked26 : annotated26.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased27 : annotated27.erase=subtree27:=by rfl

theorem masks_checked27 : annotated27.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased28 : annotated28.erase=subtree28:=by rfl

theorem masks_checked28 : annotated28.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased29 : annotated29.erase=subtree29:=by rfl

theorem masks_checked29 : annotated29.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased30 : annotated30.erase=subtree30:=by rfl

theorem masks_checked30 : annotated30.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased31 : annotated31.erase=subtree31:=by rfl

theorem masks_checked31 : annotated31.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased32 : annotated32.erase=subtree32:=by rfl

theorem masks_checked32 : annotated32.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased33 : annotated33.erase=subtree33:=by rfl

theorem masks_checked33 : annotated33.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased34 : annotated34.erase=subtree34:=by rfl

theorem masks_checked34 : annotated34.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased35 : annotated35.erase=subtree35:=by rfl

theorem masks_checked35 : annotated35.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased36 : annotated36.erase=subtree36:=by rfl

theorem masks_checked36 : annotated36.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased37 : annotated37.erase=subtree37:=by rfl

theorem masks_checked37 : annotated37.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased38 : annotated38.erase=subtree38:=by rfl

theorem masks_checked38 : annotated38.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased39 : annotated39.erase=subtree39:=by rfl

theorem masks_checked39 : annotated39.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased40 : annotated40.erase=subtree40:=by rfl

theorem masks_checked40 : annotated40.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased41 : annotated41.erase=subtree41:=by rfl

theorem masks_checked41 : annotated41.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased42 : annotated42.erase=subtree42:=by rfl

theorem masks_checked42 : annotated42.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased43 : annotated43.erase=subtree43:=by rfl

theorem masks_checked43 : annotated43.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased44 : annotated44.erase=subtree44:=by rfl

theorem masks_checked44 : annotated44.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased45 : annotated45.erase=subtree45:=by rfl

theorem masks_checked45 : annotated45.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased46 : annotated46.erase=subtree46:=by rfl

theorem masks_checked46 : annotated46.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased47 : annotated47.erase=subtree47:=by rfl

theorem masks_checked47 : annotated47.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased48 : annotated48.erase=subtree48:=by rfl

theorem masks_checked48 : annotated48.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased49 : annotated49.erase=subtree49:=by rfl

theorem masks_checked49 : annotated49.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased50 : annotated50.erase=subtree50:=by rfl

theorem masks_checked50 : annotated50.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased51 : annotated51.erase=subtree51:=by rfl

theorem masks_checked51 : annotated51.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased52 : annotated52.erase=subtree52:=by rfl

theorem masks_checked52 : annotated52.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased53 : annotated53.erase=subtree53:=by rfl

theorem masks_checked53 : annotated53.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased54 : annotated54.erase=subtree54:=by rfl

theorem masks_checked54 : annotated54.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased55 : annotated55.erase=subtree55:=by rfl

theorem masks_checked55 : annotated55.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased56 : annotated56.erase=subtree56:=by rfl

theorem masks_checked56 : annotated56.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased57 : annotated57.erase=subtree57:=by rfl

theorem masks_checked57 : annotated57.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased58 : annotated58.erase=subtree58:=by rfl

theorem masks_checked58 : annotated58.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased59 : annotated59.erase=subtree59:=by rfl

theorem masks_checked59 : annotated59.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased60 : annotated60.erase=subtree60:=by rfl

theorem masks_checked60 : annotated60.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased61 : annotated61.erase=subtree61:=by rfl

theorem masks_checked61 : annotated61.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased62 : annotated62.erase=subtree62:=by rfl

theorem masks_checked62 : annotated62.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased63 : annotated63.erase=subtree63:=by rfl

theorem masks_checked63 : annotated63.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased64 : annotated64.erase=subtree64:=by rfl

theorem masks_checked64 : annotated64.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased65 : annotated65.erase=subtree65:=by rfl

theorem masks_checked65 : annotated65.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased66 : annotated66.erase=subtree66:=by rfl

theorem masks_checked66 : annotated66.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased67 : annotated67.erase=subtree67:=by rfl

theorem masks_checked67 : annotated67.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased68 : annotated68.erase=subtree68:=by rfl

theorem masks_checked68 : annotated68.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased69 : annotated69.erase=subtree69:=by rfl

theorem masks_checked69 : annotated69.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased70 : annotated70.erase=subtree70:=by rfl

theorem masks_checked70 : annotated70.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased71 : annotated71.erase=subtree71:=by rfl

theorem masks_checked71 : annotated71.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased72 : annotated72.erase=subtree72:=by rfl

theorem masks_checked72 : annotated72.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased73 : annotated73.erase=subtree73:=by rfl

theorem masks_checked73 : annotated73.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased74 : annotated74.erase=subtree74:=by rfl

theorem masks_checked74 : annotated74.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased75 : annotated75.erase=subtree75:=by rfl

theorem masks_checked75 : annotated75.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased76 : annotated76.erase=subtree76:=by rfl

theorem masks_checked76 : annotated76.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased77 : annotated77.erase=subtree77:=by rfl

theorem masks_checked77 : annotated77.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased78 : annotated78.erase=subtree78:=by rfl

theorem masks_checked78 : annotated78.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased79 : annotated79.erase=subtree79:=by rfl

theorem masks_checked79 : annotated79.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased80 : annotated80.erase=subtree80:=by rfl

theorem masks_checked80 : annotated80.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased81 : annotated81.erase=subtree81:=by rfl

theorem masks_checked81 : annotated81.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased82 : annotated82.erase=subtree82:=by rfl

theorem masks_checked82 : annotated82.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased83 : annotated83.erase=subtree83:=by rfl

theorem masks_checked83 : annotated83.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased84 : annotated84.erase=subtree84:=by rfl

theorem masks_checked84 : annotated84.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased85 : annotated85.erase=subtree85:=by rfl

theorem masks_checked85 : annotated85.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased86 : annotated86.erase=subtree86:=by rfl

theorem masks_checked86 : annotated86.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased87 : annotated87.erase=subtree87:=by rfl

theorem masks_checked87 : annotated87.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased88 : annotated88.erase=subtree88:=by rfl

theorem masks_checked88 : annotated88.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased89 : annotated89.erase=subtree89:=by rfl

theorem masks_checked89 : annotated89.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased90 : annotated90.erase=subtree90:=by rfl

theorem masks_checked90 : annotated90.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased91 : annotated91.erase=subtree91:=by rfl

theorem masks_checked91 : annotated91.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased92 : annotated92.erase=subtree92:=by rfl

theorem masks_checked92 : annotated92.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased93 : annotated93.erase=subtree93:=by rfl

theorem masks_checked93 : annotated93.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased94 : annotated94.erase=subtree94:=by rfl

theorem masks_checked94 : annotated94.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated



theorem erased95 : annotated95.erase=subtree95:=by rfl

theorem masks_checked95 : annotated95.checkMasks=true:=by decide +kernel


end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Records
open ThreeBoundRankAnnotated

theorem annotated_erased : annotated.erase=tree:=by
  simp only [annotated,Tree.erase,erased0,erased1,erased2,erased3,erased4,erased5,erased6,erased7,erased8,erased9,erased10,erased11,erased12,erased13,erased14,erased15,erased16,erased17,erased18,erased19,erased20,erased21,erased22,erased23,erased24,erased25,erased26,erased27,erased28,erased29,erased30,erased31,erased32,erased33,erased34,erased35,erased36,erased37,erased38,erased39,erased40,erased41,erased42,erased43,erased44,erased45,erased46,erased47,erased48,erased49,erased50,erased51,erased52,erased53,erased54,erased55,erased56,erased57,erased58,erased59,erased60,erased61,erased62,erased63,erased64,erased65,erased66,erased67,erased68,erased69,erased70,erased71,erased72,erased73,erased74,erased75,erased76,erased77,erased78,erased79,erased80,erased81,erased82,erased83,erased84,erased85,erased86,erased87,erased88,erased89,erased90,erased91,erased92,erased93,erased94,erased95]
  rfl
theorem annotated_masks_checked : annotated.checkMasks=true:=by
  simp only [annotated,Tree.checkMasks,masks_checked0,masks_checked1,masks_checked2,masks_checked3,masks_checked4,masks_checked5,masks_checked6,masks_checked7,masks_checked8,masks_checked9,masks_checked10,masks_checked11,masks_checked12,masks_checked13,masks_checked14,masks_checked15,masks_checked16,masks_checked17,masks_checked18,masks_checked19,masks_checked20,masks_checked21,masks_checked22,masks_checked23,masks_checked24,masks_checked25,masks_checked26,masks_checked27,masks_checked28,masks_checked29,masks_checked30,masks_checked31,masks_checked32,masks_checked33,masks_checked34,masks_checked35,masks_checked36,masks_checked37,masks_checked38,masks_checked39,masks_checked40,masks_checked41,masks_checked42,masks_checked43,masks_checked44,masks_checked45,masks_checked46,masks_checked47,masks_checked48,masks_checked49,masks_checked50,masks_checked51,masks_checked52,masks_checked53,masks_checked54,masks_checked55,masks_checked56,masks_checked57,masks_checked58,masks_checked59,masks_checked60,masks_checked61,masks_checked62,masks_checked63,masks_checked64,masks_checked65,masks_checked66,masks_checked67,masks_checked68,masks_checked69,masks_checked70,masks_checked71,masks_checked72,masks_checked73,masks_checked74,masks_checked75,masks_checked76,masks_checked77,masks_checked78,masks_checked79,masks_checked80,masks_checked81,masks_checked82,masks_checked83,masks_checked84,masks_checked85,masks_checked86,masks_checked87,masks_checked88,masks_checked89,masks_checked90,masks_checked91,masks_checked92,masks_checked93,masks_checked94,masks_checked95]
  decide +kernel

end ThreeBoundEndpoint22Records


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
namespace ThreeBoundMinmaxNumeric.Endpoint22












theorem ordinary_seed_3_0_0 (records : List (List ℕ)) :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 0) (recipe 3 0)).eval profile3≤ rawProfile3 (.a 0 0) := by
  rw [ThreeBoundRankNumeric.rawAExpr,if_pos (by decide : 4≤ (recipe 3 0).tolerance)]
  decide +kernel

theorem ordinary_seed_3_1_1 (records : List (List ℕ)) :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 1) (recipe 3 1)).eval profile3≤ rawProfile3 (.a 1 1) := by
  rw [ThreeBoundRankNumeric.rawAExpr,if_pos (by decide : 4≤ (recipe 3 1).tolerance)]
  decide +kernel

theorem ordinary_seed_3_0_1 (records : List (List ℕ)) :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 0) (recipe 3 1)).eval profile3≤ rawProfile3 (.a 0 1) := by
  rw [ThreeBoundRankNumeric.rawAExpr,if_pos (by decide : 4≤ (recipe 3 1).tolerance)]
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_1_2 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 1) (recipe 3 2)).eval profile3≤ rawProfile3 (.a 1 2) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 1) (recipe 3 2)).eval profile3≤ bound158 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 1) (recipe 3 2) mask158 mask_correct_3_1_2
      (prepared keyCodes.get convertedValues 3) values158 bound158 coefficients_correct_3_1_2
      annotated annotated_masks_checked (all_prepared 3 (by decide)) (by decide) arithmetic_prepared158
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_1_2

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_2_2 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 2) (recipe 3 2)).eval profile3≤ rawProfile3 (.a 2 2) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 2) (recipe 3 2)).eval profile3≤ bound159 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 2) (recipe 3 2) mask159 mask_correct_3_2_2
      (prepared keyCodes.get convertedValues 3) values159 bound159 coefficients_correct_3_2_2
      annotated annotated_masks_checked (all_prepared 3 (by decide)) (by decide) arithmetic_prepared159
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_2_2

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_2_3 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 2) (recipe 3 3)).eval profile3≤ rawProfile3 (.a 2 3) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 2) (recipe 3 3)).eval profile3≤ bound161 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 2) (recipe 3 3) mask161 mask_correct_3_2_3
      (prepared keyCodes.get convertedValues 2) values161 bound161 coefficients_correct_3_2_3
      annotated annotated_masks_checked (all_prepared 2 (by decide)) (by decide) arithmetic_prepared161
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_2_3

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_3_3 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 3) (recipe 3 3)).eval profile3≤ rawProfile3 (.a 3 3) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 3) (recipe 3 3)).eval profile3≤ bound162 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 3) (recipe 3 3) mask162 mask_correct_3_3_3
      (prepared keyCodes.get convertedValues 2) values162 bound162 coefficients_correct_3_3_3
      annotated annotated_masks_checked (all_prepared 2 (by decide)) (by decide) arithmetic_prepared162
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_3_3

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_3_4 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 3) (recipe 3 4)).eval profile3≤ rawProfile3 (.a 3 4) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 3) (recipe 3 4)).eval profile3≤ bound164 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 3) (recipe 3 4) mask164 mask_correct_3_3_4
      (prepared keyCodes.get convertedValues 1) values164 bound164 coefficients_correct_3_3_4
      annotated annotated_masks_checked (all_prepared 1 (by decide)) (by decide) arithmetic_prepared164
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_3_4

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_4_4 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 4) (recipe 3 4)).eval profile3≤ rawProfile3 (.a 4 4) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 4) (recipe 3 4)).eval profile3≤ bound165 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 4) (recipe 3 4) mask165 mask_correct_3_4_4
      (prepared keyCodes.get convertedValues 1) values165 bound165 coefficients_correct_3_4_4
      annotated annotated_masks_checked (all_prepared 1 (by decide)) (by decide) arithmetic_prepared165
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_4_4

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_3_5 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 3) (recipe 3 5)).eval profile3≤ rawProfile3 (.a 3 5) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 3) (recipe 3 5)).eval profile3≤ bound167 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 3) (recipe 3 5) mask167 mask_correct_3_3_5
      (prepared keyCodes.get convertedValues 1) values167 bound167 coefficients_correct_3_3_5
      annotated annotated_masks_checked (all_prepared 1 (by decide)) (by decide) arithmetic_prepared167
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_3_5

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_5_5 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 5) (recipe 3 5)).eval profile3≤ rawProfile3 (.a 5 5) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 5) (recipe 3 5)).eval profile3≤ bound169 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 5) (recipe 3 5) mask169 mask_correct_3_5_5
      (prepared keyCodes.get convertedValues 1) values169 bound169 coefficients_correct_3_5_5
      annotated annotated_masks_checked (all_prepared 1 (by decide)) (by decide) arithmetic_prepared169
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_5_5

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_4_6 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 4) (recipe 3 6)).eval profile3≤ rawProfile3 (.a 4 6) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 4) (recipe 3 6)).eval profile3≤ bound171 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 4) (recipe 3 6) mask171 mask_correct_3_4_6
      (prepared keyCodes.get convertedValues 0) values171 bound171 coefficients_correct_3_4_6
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared171
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_4_6

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_6_6 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 6) (recipe 3 6)).eval profile3≤ rawProfile3 (.a 6 6) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 6) (recipe 3 6)).eval profile3≤ bound172 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 6) (recipe 3 6) mask172 mask_correct_3_6_6
      (prepared keyCodes.get convertedValues 0) values172 bound172 coefficients_correct_3_6_6
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared172
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_6_6

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_5_7 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 5) (recipe 3 7)).eval profile3≤ rawProfile3 (.a 5 7) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 5) (recipe 3 7)).eval profile3≤ bound173 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 5) (recipe 3 7) mask173 mask_correct_3_5_7
      (prepared keyCodes.get convertedValues 0) values173 bound173 coefficients_correct_3_5_7
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared173
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_5_7

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_7_7 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 7) (recipe 3 7)).eval profile3≤ rawProfile3 (.a 7 7) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 7) (recipe 3 7)).eval profile3≤ bound174 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 7) (recipe 3 7) mask174 mask_correct_3_7_7
      (prepared keyCodes.get convertedValues 0) values174 bound174 coefficients_correct_3_7_7
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared174
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_7_7

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_4_8 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 4) (recipe 3 8)).eval profile3≤ rawProfile3 (.a 4 8) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 4) (recipe 3 8)).eval profile3≤ bound176 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 4) (recipe 3 8) mask176 mask_correct_3_4_8
      (prepared keyCodes.get convertedValues 0) values176 bound176 coefficients_correct_3_4_8
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared176
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_4_8

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_5_8 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 5) (recipe 3 8)).eval profile3≤ rawProfile3 (.a 5 8) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 5) (recipe 3 8)).eval profile3≤ bound177 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 5) (recipe 3 8) mask177 mask_correct_3_5_8
      (prepared keyCodes.get convertedValues 0) values177 bound177 coefficients_correct_3_5_8
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared177
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_5_8

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_7_8 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 7) (recipe 3 8)).eval profile3≤ rawProfile3 (.a 7 8) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 7) (recipe 3 8)).eval profile3≤ bound178 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 7) (recipe 3 8) mask178 mask_correct_3_7_8
      (prepared keyCodes.get convertedValues 0) values178 bound178 coefficients_correct_3_7_8
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared178
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_7_8

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_8_8 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 8) (recipe 3 8)).eval profile3≤ rawProfile3 (.a 8 8) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 8) (recipe 3 8)).eval profile3≤ bound179 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 8) (recipe 3 8) mask179 mask_correct_3_8_8
      (prepared keyCodes.get convertedValues 0) values179 bound179 coefficients_correct_3_8_8
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared179
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_8_8

theorem raw_seed_3_9_9 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 9) (recipe 3 9)).eval profile3≤ rawProfile3 (.a 9 9) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 9) (recipe 3 9)).eval profile3≤ bound179 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 9) (recipe 3 9) mask179 mask_correct_3_9_9
      (prepared keyCodes.get convertedValues 0) values179 bound179 coefficients_correct_3_9_9
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared179
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_9_9

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_10_10 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 10) (recipe 3 10)).eval profile3≤ rawProfile3 (.a 10 10) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 10) (recipe 3 10)).eval profile3≤ bound180 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 10) (recipe 3 10) mask180 mask_correct_3_10_10
      (prepared keyCodes.get convertedValues 0) values180 bound180 coefficients_correct_3_10_10
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared180
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_10_10

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_10_11 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 10) (recipe 3 11)).eval profile3≤ rawProfile3 (.a 10 11) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 10) (recipe 3 11)).eval profile3≤ bound182 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 10) (recipe 3 11) mask182 mask_correct_3_10_11
      (prepared keyCodes.get convertedValues 0) values182 bound182 coefficients_correct_3_10_11
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared182
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_10_11

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_11_11 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 11) (recipe 3 11)).eval profile3≤ rawProfile3 (.a 11 11) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 11) (recipe 3 11)).eval profile3≤ bound183 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 11) (recipe 3 11) mask183 mask_correct_3_11_11
      (prepared keyCodes.get convertedValues 0) values183 bound183 coefficients_correct_3_11_11
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared183
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_11_11

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_11_12 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 11) (recipe 3 12)).eval profile3≤ rawProfile3 (.a 11 12) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 11) (recipe 3 12)).eval profile3≤ bound185 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 11) (recipe 3 12) mask185 mask_correct_3_11_12
      (prepared keyCodes.get convertedValues 0) values185 bound185 coefficients_correct_3_11_12
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared185
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_11_12

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_12_12 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 12) (recipe 3 12)).eval profile3≤ rawProfile3 (.a 12 12) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 12) (recipe 3 12)).eval profile3≤ bound186 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 12) (recipe 3 12) mask186 mask_correct_3_12_12
      (prepared keyCodes.get convertedValues 0) values186 bound186 coefficients_correct_3_12_12
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared186
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_12_12

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_10_13 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 10) (recipe 3 13)).eval profile3≤ rawProfile3 (.a 10 13) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 10) (recipe 3 13)).eval profile3≤ bound187 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 10) (recipe 3 13) mask187 mask_correct_3_10_13
      (prepared keyCodes.get convertedValues 0) values187 bound187 coefficients_correct_3_10_13
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared187
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_10_13

theorem raw_seed_3_11_14 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 11) (recipe 3 14)).eval profile3≤ rawProfile3 (.a 11 14) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 11) (recipe 3 14)).eval profile3≤ bound187 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 11) (recipe 3 14) mask187 mask_correct_3_11_14
      (prepared keyCodes.get convertedValues 0) values187 bound187 coefficients_correct_3_11_14
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared187
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_11_14

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_12_13 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 12) (recipe 3 13)).eval profile3≤ rawProfile3 (.a 12 13) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 12) (recipe 3 13)).eval profile3≤ bound188 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 12) (recipe 3 13) mask188 mask_correct_3_12_13
      (prepared keyCodes.get convertedValues 0) values188 bound188 coefficients_correct_3_12_13
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared188
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_12_13

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_13_13 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 13) (recipe 3 13)).eval profile3≤ rawProfile3 (.a 13 13) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 13) (recipe 3 13)).eval profile3≤ bound189 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 13) (recipe 3 13) mask189 mask_correct_3_13_13
      (prepared keyCodes.get convertedValues 0) values189 bound189 coefficients_correct_3_13_13
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared189
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_13_13

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_13_14 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 13) (recipe 3 14)).eval profile3≤ rawProfile3 (.a 13 14) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 13) (recipe 3 14)).eval profile3≤ bound190 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 13) (recipe 3 14) mask190 mask_correct_3_13_14
      (prepared keyCodes.get convertedValues 0) values190 bound190 coefficients_correct_3_13_14
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared190
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_13_14

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_14_14 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 14) (recipe 3 14)).eval profile3≤ rawProfile3 (.a 14 14) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 14) (recipe 3 14)).eval profile3≤ bound191 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 14) (recipe 3 14) mask191 mask_correct_3_14_14
      (prepared keyCodes.get convertedValues 0) values191 bound191 coefficients_correct_3_14_14
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared191
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_14_14

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_15_15 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 15) (recipe 3 15)).eval profile3≤ rawProfile3 (.a 15 15) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 15) (recipe 3 15)).eval profile3≤ bound194 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 15) (recipe 3 15) mask194 mask_correct_3_15_15
      (prepared keyCodes.get convertedValues 0) values194 bound194 coefficients_correct_3_15_15
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared194
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_15_15

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_5_16 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 5) (recipe 3 16)).eval profile3≤ rawProfile3 (.a 5 16) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 5) (recipe 3 16)).eval profile3≤ bound195 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 5) (recipe 3 16) mask195 mask_correct_3_5_16
      (prepared keyCodes.get convertedValues 0) values195 bound195 coefficients_correct_3_5_16
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared195
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_5_16

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
theorem raw_seed_3_16_16 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 16) (recipe 3 16)).eval profile3≤ rawProfile3 (.a 16 16) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 16) (recipe 3 16)).eval profile3≤ bound200 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 16) (recipe 3 16) mask200 mask_correct_3_16_16
      (prepared keyCodes.get convertedValues 0) values200 bound200 coefficients_correct_3_16_16
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared200
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_16_16

theorem raw_seed_3_17_17 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 17) (recipe 3 17)).eval profile3≤ rawProfile3 (.a 17 17) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 17) (recipe 3 17)).eval profile3≤ bound200 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 17) (recipe 3 17) mask200 mask_correct_3_17_17
      (prepared keyCodes.get convertedValues 0) values200 bound200 coefficients_correct_3_17_17
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared200
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_17_17

theorem raw_seed_3_18_18 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 18) (recipe 3 18)).eval profile3≤ rawProfile3 (.a 18 18) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 18) (recipe 3 18)).eval profile3≤ bound200 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 18) (recipe 3 18) mask200 mask_correct_3_18_18
      (prepared keyCodes.get convertedValues 0) values200 bound200 coefficients_correct_3_18_18
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared200
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_18_18

theorem raw_seed_3_19_19 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 19) (recipe 3 19)).eval profile3≤ rawProfile3 (.a 19 19) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 19) (recipe 3 19)).eval profile3≤ bound200 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 19) (recipe 3 19) mask200 mask_correct_3_19_19
      (prepared keyCodes.get convertedValues 0) values200 bound200 coefficients_correct_3_19_19
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared200
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_19_19

theorem raw_seed_3_20_20 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 20) (recipe 3 20)).eval profile3≤ rawProfile3 (.a 20 20) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 20) (recipe 3 20)).eval profile3≤ bound200 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 20) (recipe 3 20) mask200 mask_correct_3_20_20
      (prepared keyCodes.get convertedValues 0) values200 bound200 coefficients_correct_3_20_20
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared200
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_20_20

theorem raw_seed_3_21_21 :
    (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
      (recipe 3 21) (recipe 3 21)).eval profile3≤ rawProfile3 (.a 21 21) := by
  have h : (ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 annotated.erase.elements
      (recipe 3 21) (recipe 3 21)).eval profile3≤ bound200 :=
    rawA_le_of_annotated 22 profile3 ThreeBoundOrdinary5591.numericCaps 14
      (recipe 3 21) (recipe 3 21) mask200 mask_correct_3_21_21
      (prepared keyCodes.get convertedValues 0) values200 bound200 coefficients_correct_3_21_21
      annotated annotated_masks_checked (all_prepared 0 (by decide)) (by decide) arithmetic_prepared200
  rw [annotated_erased] at h
  exact h.trans bound_transfer_3_21_21

end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records

theorem seed_bounds3 : ThreeBoundEndpoint22Hybrid.SeedBounds records 3 profile3 rawProfile3 aSeeds3 := by
  intro pair hp
  simp only [aSeeds3,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide,ordinary_seed_3_0_0 records⟩
  · exact ⟨by decide,ordinary_seed_3_1_1 records⟩
  · exact ⟨by decide,raw_seed_3_2_2⟩
  · exact ⟨by decide,raw_seed_3_3_3⟩
  · exact ⟨by decide,raw_seed_3_4_4⟩
  · exact ⟨by decide,raw_seed_3_5_5⟩
  · exact ⟨by decide,raw_seed_3_6_6⟩
  · exact ⟨by decide,raw_seed_3_7_7⟩
  · exact ⟨by decide,raw_seed_3_8_8⟩
  · exact ⟨by decide,raw_seed_3_9_9⟩
  · exact ⟨by decide,raw_seed_3_10_10⟩
  · exact ⟨by decide,raw_seed_3_11_11⟩
  · exact ⟨by decide,raw_seed_3_12_12⟩
  · exact ⟨by decide,raw_seed_3_13_13⟩
  · exact ⟨by decide,raw_seed_3_14_14⟩
  · exact ⟨by decide,raw_seed_3_15_15⟩
  · exact ⟨by decide,raw_seed_3_16_16⟩
  · exact ⟨by decide,raw_seed_3_17_17⟩
  · exact ⟨by decide,raw_seed_3_18_18⟩
  · exact ⟨by decide,raw_seed_3_19_19⟩
  · exact ⟨by decide,raw_seed_3_20_20⟩
  · exact ⟨by decide,raw_seed_3_21_21⟩
  · exact ⟨by decide,ordinary_seed_3_0_1 records⟩
  · exact ⟨by decide,raw_seed_3_1_2⟩
  · exact ⟨by decide,raw_seed_3_2_3⟩
  · exact ⟨by decide,raw_seed_3_3_4⟩
  · exact ⟨by decide,raw_seed_3_7_8⟩
  · exact ⟨by decide,raw_seed_3_10_11⟩
  · exact ⟨by decide,raw_seed_3_11_12⟩
  · exact ⟨by decide,raw_seed_3_12_13⟩
  · exact ⟨by decide,raw_seed_3_13_14⟩
  · exact ⟨by decide,raw_seed_3_3_5⟩
  · exact ⟨by decide,raw_seed_3_4_6⟩
  · exact ⟨by decide,raw_seed_3_5_7⟩
  · exact ⟨by decide,raw_seed_3_5_8⟩
  · exact ⟨by decide,raw_seed_3_10_13⟩
  · exact ⟨by decide,raw_seed_3_11_14⟩
  · exact ⟨by decide,raw_seed_3_4_8⟩
  · exact ⟨by decide,raw_seed_3_5_16⟩
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
Sensitivity213981Formal.ThreeBoundEndpoint22Hybrid.SeedBounds
  Sensitivity213981Formal.ThreeBoundEndpoint22Records.records
  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 3)))
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.profile3
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.rawProfile3
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.aSeeds3 := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.seed_bounds3
