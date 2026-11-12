-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCode_dual_dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:52:35.727196+00:00
-- url     : https://prove2.me/submissions/b45e002e-11bf-4b06-9323-687007607701

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Coding_LinearCode_dimension_add_dual_dimension_eq_length
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    R.rowCode.dual.dual.carrier = R.rowCode.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (R.rowCode_le_dual_dual)
  change Dimension R.rowCode = Dimension R.rowCode.dual.dual
  have h₁ := R.rowCode.dimension_add_dual_dimension_eq_length
  have h₂ := R.rowCode.dual.dimension_add_dual_dimension_eq_length
  omega
end QEC.Distillation.Triorthogonal.BinaryRowFamily
