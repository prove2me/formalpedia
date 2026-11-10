-- Prove2me | solution 1 for QEC.Coding.BDL26AlternatingCochain.map_commutes1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:23:44.126507+00:00
-- url     : https://prove2.me/submissions/de3d732e-b451-488d-9d60-1459fb0d5d9c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes1
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_finiteCoordinateComposite_commutes


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph
namespace QEC.Coding.BDL26AlternatingCochain
theorem _root_.solution (S : OddScale) (n : Nat) :
    (tannerCoboundary1 (state S n).presentation).comp (map1 S n) =
      (map2 S n).comp (tannerCoboundary1 (state S 0).presentation) := by
  exact finiteCoordinateComposite_commutes (stepMap1 S) (stepMap2 S)
    (fun k => tannerCoboundary1 (state S k).presentation)
    (fun k => nextMap_commutes1 S k (state S k)) n
end QEC.Coding.BDL26AlternatingCochain
