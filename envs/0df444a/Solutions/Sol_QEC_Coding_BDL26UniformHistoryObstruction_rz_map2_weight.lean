-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.rz_map2_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:45:52.864229+00:00
-- url     : https://prove2.me/submissions/d57f8926-915d-4af1-b303-ea6bf3292a33

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_rz_root_injective
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_rz_map2_support

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z) :
    HammingWeight (map2Coord P A S s) = HammingWeight s := by
  classical
  change (hammingSupport (map2Coord P A S s)).card = (hammingSupport s).card
  rw [rz_map2_support]
  exact Finset.card_image_of_injective _ (rz_root_injective P A S)
end QEC.Coding.BDL26UniformHistoryObstruction
