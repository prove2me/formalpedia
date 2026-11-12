-- Prove2me | solution 1 for QEC.Coding.BDL26AlternatingCochain.map_commutes0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:01:50.875682+00:00
-- url     : https://prove2.me/submissions/2af7de50-a41a-48ab-9208-7e7abd9a265a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_finiteCoordinateComposite_commutes


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph
namespace QEC.Coding.BDL26AlternatingCochain
theorem _root_.solution (S : OddScale) (n : Nat) :
    (tannerCoboundary0 (state S n).presentation).comp (map0 S n) =
      (map1 S n).comp (tannerCoboundary0 (state S 0).presentation) := by
  exact finiteCoordinateComposite_commutes (stepMap0 S) (stepMap1 S)
    (fun k => tannerCoboundary0 (state S k).presentation)
    (fun k => nextMap_commutes0 S k (state S k)) n
end QEC.Coding.BDL26AlternatingCochain
