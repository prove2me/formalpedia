-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.span_reducedRows_eq_rowCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:58:26.096771+00:00
-- url     : https://prove2.me/submissions/9509b75f-0397-4e82-9af1-04454a1b8b2a

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_span_evenBasis_eq_evenCode

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
    Submodule.span (ZMod 2) (Set.range R.reducedRow) = R.rowCode.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨r, rfl⟩
    rcases r with a | b
    · exact R.row_mem_rowCode (.inl a)
    · rw [R.rowCode_eq_evenCode_sup_oddCode]
      exact Submodule.mem_sup_left (R.evenBasis b).property
  · rw [R.rowCode_eq_evenCode_sup_oddCode]
    apply sup_le
    · rw [← R.span_evenBasis_eq_evenCode]
      apply Submodule.span_mono
      rintro x ⟨b, rfl⟩
      exact ⟨Sum.inr b, rfl⟩
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
end QEC.Distillation.Triorthogonal.BinaryRowFamily
