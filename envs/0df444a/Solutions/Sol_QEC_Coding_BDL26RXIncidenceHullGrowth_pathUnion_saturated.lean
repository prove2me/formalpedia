-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.pathUnion_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:40:37.561203+00:00
-- url     : https://prove2.me/submissions/dcdef1d7-f519-414a-a43b-ec1ce87d3a4e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_pathUnion

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (seed : Finset (state S i.val).presentation.Q) :
    IncidenceSaturated S depth i (pathUnion S depth i seed) := by
  intro q hq r z left right
  obtain ⟨a,ha,path⟩ := (mem_pathUnion S depth i seed q).mp hq
  exact (mem_pathUnion S depth i seed r).mpr ⟨a,ha,.snoc path z left right⟩
end QEC.Coding.BDL26RXIncidenceHullGrowth
