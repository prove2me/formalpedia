-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.product_cartesian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:53:12.091688+00:00
-- url     : https://prove2.me/submissions/64f7ab44-c421-4f35-904b-4a7857436234

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_mem_localWords

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
theorem _root_.solution (S : OddScale) (depth : ℕ)
    (T : Finset (decodingGraph S depth).Node) (t : ℝ) :
    (∏ v ∈ T, factor S v.1.val v.2 t) =
      ∑ x : (∀ v : T, {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0}),
        Real.exp (-t*(∑ v : T,
          (HammingWeight (extend S v.val.1.val v.val.2 (x v).val) : ℝ))) := by
  have hprod : (∏ v ∈ T, factor S v.1.val v.2 t) =
      ∏ v : T, ∑ w : {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0},
        Real.exp (-t*(HammingWeight (extend S v.val.1.val v.val.2 w.val) : ℝ)) := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro v hv
    unfold factor fiberFactor
    exact Finset.sum_subtype _ (fun x => mem_localWords S _ _ x) _
  rw [hprod,Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
end QEC.Coding.BDL26ConnectedSyndromeMass
