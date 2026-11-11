-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:50:22.791206+00:00
-- url     : https://prove2.me/submissions/72298b2e-328a-4644-811f-629ab06f5b29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_basis_coboundary_weight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerError_eq_basis


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val =
      qZDegree (state S (2 * j + 3)).presentation (lowerBasis S j) := by
  change HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j)) = _
  rw [indexedFamily_coboundary1, lowerError_eq_basis]
  exact basis_coboundary_weight _ _
end QEC.Coding.BDL26UniformHistoryObstruction
