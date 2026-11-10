-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.fiberRegion_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:29:18.582207+00:00
-- url     : https://prove2.me/submissions/bef1401c-88b7-4c38-b580-05e8a176efeb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
variable {Label Coordinate : Type} [Fintype Label] [Fintype Coordinate]
  [DecidableEq Label] [DecidableEq Coordinate]
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution (owner : Coordinate → Label)
    {first second : Label} (hne : first ≠ second) :
    Disjoint (fiberRegion owner first) (fiberRegion owner second) := by
  apply Finset.disjoint_left.mpr
  intro coordinate hfirst hsecond
  exact hne ((Finset.mem_filter.mp hfirst).2.symm.trans
    (Finset.mem_filter.mp hsecond).2)
end QEC.Coding.BDL26ReplacementSupport
