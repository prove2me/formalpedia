-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.commuting_pair_contains_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:49:02.164746+00:00
-- url     : https://prove2.me/submissions/1e1fd9d3-3a6a-4df9-8aec-e4e5ef187881

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_mem_incidenceHull_iff_path
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_le_every_commuting_pair


set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (h : i.val % 2 = 0)
    (seed A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed ⊆ A)
    (commutes : ∀ w, MultiscaleDecoder.maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (MultiscaleDecoder.maskWord A w))
    {q r : (state S i.val).presentation.Q} (hq : q ∈ seed)
    (path : SharedZPath (state S i.val).presentation q r) : r ∈ A := by
  exact (incidenceHull_le_every_commuting_pair S depth i h seed A B hseed commutes).1
    ((mem_incidenceHull_iff_path S depth i seed r).mpr ⟨q,hq,path⟩)
end QEC.Coding.BDL26RXIncidenceHullGrowth
