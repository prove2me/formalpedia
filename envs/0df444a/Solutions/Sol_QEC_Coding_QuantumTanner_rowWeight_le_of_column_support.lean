-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.rowWeight_le_of_column_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:49:01.24566+00:00
-- url     : https://prove2.me/submissions/f56070bf-9c74-47cf-b8ea-a6f0c12e87cf

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (c : Word (ZMod 2) (A × B)) (columns : Finset B)
    (hSupport : ∀ b, b ∉ columns → columnRestriction b c = 0) (a : A) :
    HammingWeight (rowRestriction a c) ≤ columns.card := by
  apply Finset.card_le_card
  intro b hb
  by_contra hNot
  exact (Finset.mem_filter.mp hb).2 (congrFun (hSupport b hNot) a)
end QEC.Coding.QuantumTanner
