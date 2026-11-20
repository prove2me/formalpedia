-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.oldX_parity_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:39.925738+00:00
-- url     : https://prove2.me/submissions/17a5aa2b-b359-4e90-9ef4-105b3055c8a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_raw_star_cover

section
noncomputable section
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
private theorem supported_incidence (S : OddScale) (u : RZX (P S) S) (h : Error S)
    (hh : supported S u h) (r : RZQ (P S) S) (hr : h r≠0) :
    rzXQIncidence (P S) (A S).toTannerSquareAdmissible S u r=true := by
  have hm := hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
  exact (Finset.mem_filter.mp hm).2
private theorem supported_Q_labels (S : OddScale) (u : RZX (P S) S) (h : Error S)
    (hh : supported S u h) (q : (P S).Q)
    (v : QDoubleCylinderVertex (transposePresentation (P S)) q S) (hv : h (.inr ⟨q,v⟩)≠0) :
    q ∈ BDL26RZPhysicalXStarTransport.rawQ0 (P S) S u := by
  have hs := BDL26RZPhysicalXStarTransport.raw_star_cover (P S)
    (A S).toTannerSquareAdmissible S u (.inr ⟨q,v⟩)
    (supported_incidence S u h hh _ hv)
  exact (BDL26RZFiniteBlockTransport.Coordinates.mem_input_q _ _ _ _ _ _).1 hs
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (x : (P S).X) (copy : BDL26FiniteTannerSquare.Two)
    (h : Error S) (hh : supported S (.inr (x,copy)) h) (q : (P S).Q)
    (hq : parity S h q≠0) :
    q ∈ BDL26RXPhysicalStarTransport.physicalXStar (P S) x := by
  by_contra hn
  apply hq
  change (∑ v : QDoubleCylinderVertex (transposePresentation (P S)) q S,
    h (.inr ⟨q,v⟩))=0
  apply Finset.sum_eq_zero
  intro v _
  by_contra hv
  exact hn (supported_Q_labels S _ h hh q v hv)
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
