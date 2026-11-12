-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.commuting_pair_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:54:05.152177+00:00
-- url     : https://prove2.me/submissions/b15044cd-3507-4c59-92dd-795eb106d64b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_singleton_hull_card_lower
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_le_every_commuting_pair
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks
namespace QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed S i.val ⊆ A)
    (commutes : ∀ w, MultiscaleDecoder.maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (MultiscaleDecoder.maskWord A w)) :
    5*2^i.val ≤ A.card :=
  (singleton_hull_card_lower S depth i).trans
    (Finset.card_le_card
      (incidenceHull_le_every_commuting_pair S depth i h _ A B hseed commutes).1)
end QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
