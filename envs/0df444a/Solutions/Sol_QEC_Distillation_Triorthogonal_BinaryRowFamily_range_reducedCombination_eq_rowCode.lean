-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.range_reducedCombination_eq_rowCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:00:46.747204+00:00
-- url     : https://prove2.me/submissions/57cf13ae-d59a-4c37-b5d3-4d754b6a84fa

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_span_reducedRows_eq_rowCode

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) :
    LinearMap.range R.reducedCombination = R.rowCode.carrier := by
  rw [reducedCombination, Fintype.range_linearCombination,
    R.span_reducedRows_eq_rowCode]
end QEC.Distillation.Triorthogonal.BinaryRowFamily
