-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.rowCode_eq_stabilizerCode_sup_logicalCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:37.54561+00:00
-- url     : https://prove2.me/submissions/258a7edf-2a27-45c9-afbf-0a808a3f3d46

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]
namespace QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
theorem _root_.solution
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.rowCode.carrier =
      R.stabilizerCode.carrier ⊔ R.logicalCode.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨index, rfl⟩
    rcases index with a | s
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨s, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr s, rfl⟩
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
