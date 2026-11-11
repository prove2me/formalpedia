-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.incidenceHull_eq_pathUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:46:07.766204+00:00
-- url     : https://prove2.me/submissions/1307b6d9-33c1-4403-8dec-e8a2540cecfe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_pathUnion
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_path_mem_of_saturated
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_pathUnion_saturated
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_minimal
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_saturated
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_subset_incidenceHull


set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (seed : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i seed = pathUnion S depth i seed := by
  apply Finset.Subset.antisymm
  · apply incidenceHull_minimal S depth i seed
    · intro q hq
      exact (mem_pathUnion S depth i seed q).mpr ⟨q,hq,.refl q⟩
    · exact pathUnion_saturated S depth i seed
  · intro r hr
    obtain ⟨q,hq,path⟩ := (mem_pathUnion S depth i seed r).mp hr
    exact path_mem_of_saturated S depth i _ (incidenceHull_saturated S depth i seed)
      (subset_incidenceHull S depth i seed hq) path
end QEC.Coding.BDL26RXIncidenceHullGrowth
