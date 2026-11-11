-- Prove2me | solution 1 for QEC.Coding.BDL26RXInfluenceBounds.input_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:59:32.331862+00:00
-- url     : https://prove2.me/submissions/33695fdd-55a8-41f0-af3e-5fd77954c3a7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_error_coboundary_zero_on_readRegion

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
namespace QEC.Coding.BDL26RXInfluenceBounds
theorem _root_.solution (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) :
    sigma.val p = (sigmaPlusError S depth i sigma e).val p := by
  change sigma.val p = sigma.val p + (indexedFamily S depth).coboundary1 i.succ e p
  rw [error_coboundary_zero_on_readRegion S depth i h e z hz p hp, add_zero]
end QEC.Coding.BDL26RXInfluenceBounds
