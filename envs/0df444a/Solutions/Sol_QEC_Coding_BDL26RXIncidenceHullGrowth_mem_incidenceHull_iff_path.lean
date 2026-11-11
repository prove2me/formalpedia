-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.mem_incidenceHull_iff_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:53:04.26977+00:00
-- url     : https://prove2.me/submissions/0e444424-7f6e-45ce-92eb-7ebb685e092f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_pathUnion
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_incidenceHull_eq_pathUnion

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (seed : Finset (state S i.val).presentation.Q)
    (r : (state S i.val).presentation.Q) :
    r ∈ incidenceHull S depth i seed ↔
      ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r := by
  rw [incidenceHull_eq_pathUnion]
  exact mem_pathUnion S depth i seed r
end QEC.Coding.BDL26RXIncidenceHullGrowth
