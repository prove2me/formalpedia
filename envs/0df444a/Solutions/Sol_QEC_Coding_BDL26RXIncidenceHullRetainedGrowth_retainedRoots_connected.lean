-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullRetainedGrowth.retainedRoots_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:24:47.459044+00:00
-- url     : https://prove2.me/submissions/d8b9aa9e-7779-413e-b4df-afb7df85fbb4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_nextRoots_paths
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_base_path


set_option autoImplicit false
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks
namespace QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
theorem _root_.solution (S : OddScale) (n : Nat) (a b : Retained n) :
    SharedZPath (state S n).presentation (retainedRoots S n a) (retainedRoots S n b) := by
  induction n with
  | zero => exact base_path a b
  | succ n ih =>
      exact nextRoots_paths S n (state S n) (ih a.1 b.1) a.2 b.2
end QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
