-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.columnWeight_le_of_row_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:49:04.170494+00:00
-- url     : https://prove2.me/submissions/d1f6198d-9d26-4673-ab43-e4af7de077fd

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
    (r : Word (ZMod 2) (A × B)) (rows : Finset A)
    (hSupport : ∀ a, a ∉ rows → rowRestriction a r = 0) (b : B) :
    HammingWeight (columnRestriction b r) ≤ rows.card := by
  apply Finset.card_le_card
  intro a ha
  by_contra hNot
  exact (Finset.mem_filter.mp ha).2 (congrFun (hSupport a hNot) b)
end QEC.Coding.QuantumTanner
