-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.rz_root_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:38:29.054399+00:00
-- url     : https://prove2.me/submissions/92741cc3-a566-4774-afe1-bdd980ab395f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    Function.Injective (fun z : P.Z => (⟨z, rzMap1ZRoot P A z S⟩ : RZZ P S)) := by
  intro z w h
  exact congrArg Sigma.fst h
end QEC.Coding.BDL26UniformHistoryObstruction
