-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.factor_eq_original_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:57:31.624734+00:00
-- url     : https://prove2.me/submissions/ffa3568c-beb4-4f8e-9036-40381254d9e0

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberFactor_eq_image


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
namespace QEC.Coding.BDL26ConnectedSyndromeMass
theorem _root_.solution (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) :
    factor S i u t = weightedFamily ((localWords S i u).image (extend S i u)) t :=
  fiberFactor_eq_image (owner S i) u _ t
end QEC.Coding.BDL26ConnectedSyndromeMass
