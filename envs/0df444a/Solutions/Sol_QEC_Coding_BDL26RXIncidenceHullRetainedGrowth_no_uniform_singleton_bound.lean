-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.no_uniform_singleton_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:49:51.759783+00:00
-- url     : https://prove2.me/submissions/c66ea296-8893-4ad5-af71-7c942c0454d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_seed_card
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_singleton_hull_card_lower

set_option autoImplicit false
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks
namespace QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
theorem _root_.solution (S : OddScale) (C : Nat) :
    ∃ (depth : Nat) (i : StepIndex depth), i.val % 2 = 0 ∧
      (seed S i.val).card = 1 ∧ C < (incidenceHull S depth i (seed S i.val)).card := by
  let m := 2*(C+1)
  let i : StepIndex (m+1) := ⟨m,by omega⟩
  refine ⟨m+1,i,?_,seed_card S i.val,?_⟩
  · change (2*(C+1)) % 2 = 0
    omega
  · have hg := singleton_hull_card_lower S (m+1) i
    have hp : i.val < 2^i.val := i.val.lt_two_pow_self
    have hm : C < i.val := by change C < 2*(C+1); omega
    omega
end QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
