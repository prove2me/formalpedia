-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:08:26.179609+00:00
-- url     : https://prove2.me/submissions/f182c4f3-7d61-41be-8c2c-1b56508d12fa

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_extend_weight
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_mem_localWords
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_card
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_weightedFamily_bounds


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
    0≤factor S i u t ∧ factor S i u t≤envelope S t := by
  have heq : factor S i u t=weightedFamily (localWords S i u) t := by
    unfold factor fiberFactor weightedFamily
    apply Finset.sum_congr rfl
    intro x _
    rw [show HammingWeight (fiberExtend (owner S i) u x)=HammingWeight x from
      extend_weight S i u x]
  rw [heq]
  change 0≤weightedFamily (localWords S i u) t ∧
    weightedFamily (localWords S i u) t≤(1+Real.exp (-t))^(14*S.ell^2)-1
  exact weightedFamily_bounds _ t (fun x hx => (mem_localWords S i u x).mp hx)
    (14*S.ell^2) (ownerFiber_card S i u)
end QEC.Coding.BDL26ConnectedSyndromeMass
