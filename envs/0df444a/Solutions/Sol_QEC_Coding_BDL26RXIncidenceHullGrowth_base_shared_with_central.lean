-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.base_shared_with_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:36:08.549284+00:00
-- url     : https://prove2.me/submissions/6dc27ba1-3db7-4dcd-9f69-5f9231fa966c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (q : BaseQubit) :
    ∃ z : BaseZ, baseTannerSquarePresentation.qz q z = true ∧
      baseTannerSquarePresentation.qz (4 : BaseQubit) z = true := by
  have incident (a : BaseQubit) (z : BaseZ) (h : baseBoundary2Matrix a z ≠ 0) :
      baseTannerSquarePresentation.qz a z = true := by
    change decide (baseBoundary2Matrix a z ≠ 0) = true
    rw [decide_eq_true_eq]
    exact h
  fin_cases q
  · exact ⟨0,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨1,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨0,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨1,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
  · exact ⟨0,incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero),
      incident _ _ (by change (1 : BDL26FiniteAlternatingCore.Field) ≠ 0; exact one_ne_zero)⟩
end QEC.Coding.BDL26RXIncidenceHullGrowth
