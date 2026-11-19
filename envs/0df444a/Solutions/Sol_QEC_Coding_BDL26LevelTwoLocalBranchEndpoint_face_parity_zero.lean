-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.face_parity_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:56.640094+00:00
-- url     : https://prove2.me/submissions/15f4c7b5-f8dc-46e0-be55-a55cc3972370

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
theorem _root_.solution (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) : parity S h=0 := by
  funext q
  change (∑ v : QDoubleCylinderVertex (transposePresentation (P S)) q S,
    h (.inr ⟨q,v⟩))=0
  apply Finset.sum_eq_zero
  intro v _
  by_contra hv
  have hm := supported_Q_labels S _ h hh q v hv
  change q ∈ (∅ : Finset (P S).Q) at hm
  exact Finset.notMem_empty q hm
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
