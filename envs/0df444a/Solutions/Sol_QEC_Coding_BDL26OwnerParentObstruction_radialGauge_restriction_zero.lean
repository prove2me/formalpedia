-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerParentObstruction.radialGauge_restriction_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:52:41.312221+00:00
-- url     : https://prove2.me/submissions/be428aa5-f0ff-4166-9b67-bc5e2a58cce6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_connectingWeight_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators
namespace QEC.Coding.BDL26OwnerParentObstruction
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (selected : Fin 2) (alpha : Neighbor P x → BDL26Field)
    (q : P.Q) (hq : P.xq x q = true) :
    rxXQDegreeOne P A q x hq S (radialGauge P A x S selected alpha) = 0 := by
  have hz := radialGauge_connectingWeight_zero P A x S selected alpha
  have hle := Finset.single_le_sum (fun (r : Neighbor P x) _ =>
    Nat.zero_le (HammingWeight (rxXQDegreeOne P A r.val x r.property S
      (radialGauge P A x S selected alpha)))) (Finset.mem_univ (⟨q,hq⟩ : Neighbor P x))
  change HammingWeight (rxXQDegreeOne P A q x hq S
    (radialGauge P A x S selected alpha)) ≤ connectingWeight P A x S _ at hle
  rw [hz] at hle
  exact (HammingWeight_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hle)
end QEC.Coding.BDL26OwnerParentObstruction
