-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.exists_reducedCombination_of_mem_rowCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:13:55.000425+00:00
-- url     : https://prove2.me/submissions/61bff814-379e-4189-bb57-02cd8b73c1c4

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_range_reducedCombination_eq_rowCode

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
    (R : BinaryRowFamily OddRow EvenRow Col)
    {f : Word (ZMod 2) Col} (hf : f ∈ R.rowCode.carrier) :
    ∃ c : Word (ZMod 2) R.ReducedRowIndex,
      R.reducedCombination c = f := by
  have hrange : f ∈ LinearMap.range R.reducedCombination := by
    rw [R.range_reducedCombination_eq_rowCode]
    exact hf
  exact hrange
end QEC.Distillation.Triorthogonal.BinaryRowFamily
