-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.envelope_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:27:40.072986+00:00
-- url     : https://prove2.me/submissions/74256f78-8d28-4280-a194-41caf36ca852

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass

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
theorem _root_.solution (S : OddScale) (t : ℝ) : 0≤envelope S t := by
  have hp : (1 : ℝ)≤1+Real.exp (-t) := by linarith [Real.exp_pos (-t)]
  have h : (1 : ℝ) ≤ (1+Real.exp (-t))^(14*S.ell^2) := one_le_pow₀ hp
  unfold envelope
  linarith
end QEC.Coding.BDL26ConnectedSyndromeMass
