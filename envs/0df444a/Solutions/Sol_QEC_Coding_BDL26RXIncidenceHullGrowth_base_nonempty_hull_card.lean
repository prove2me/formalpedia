-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.base_nonempty_hull_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:49:23.845437+00:00
-- url     : https://prove2.me/submissions/bde97bff-8d50-4190-9b44-632b40032ee2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_base_nonempty_hull
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (seed : Finset BaseQubit) (hne : seed.Nonempty)
    (hd : 0 < depth) : (incidenceHull S depth ⟨0,hd⟩ seed).card = 5 := by
  rw [base_nonempty_hull S depth seed hne hd]
  exact Finset.card_univ.trans baseQubit_card
end QEC.Coding.BDL26RXIncidenceHullGrowth
