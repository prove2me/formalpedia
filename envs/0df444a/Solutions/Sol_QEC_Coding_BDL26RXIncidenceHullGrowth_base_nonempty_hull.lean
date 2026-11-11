-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.base_nonempty_hull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:03:51.42465+00:00
-- url     : https://prove2.me/submissions/49081e80-95ff-4f51-ac9e-3d9396b6bc18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_incidenceHull_iff_path
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_base_path

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (seed : Finset BaseQubit) (hne : seed.Nonempty)
    (hd : 0 < depth) : incidenceHull S depth ⟨0,hd⟩ seed = Finset.univ := by
  obtain ⟨q,hq⟩ := hne
  apply Finset.eq_univ_of_forall
  intro r
  exact (mem_incidenceHull_iff_path S depth ⟨0,hd⟩ seed r).mpr ⟨q,hq,base_path q r⟩
end QEC.Coding.BDL26RXIncidenceHullGrowth
