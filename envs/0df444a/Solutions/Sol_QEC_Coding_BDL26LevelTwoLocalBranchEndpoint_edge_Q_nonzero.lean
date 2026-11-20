-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_Q_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:58.287688+00:00
-- url     : https://prove2.me/submissions/3fa79961-feb4-4330-866d-0c125c69cc70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
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
theorem _root_.solution (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h)
    (v : QDoubleCylinderVertex (transposePresentation (P S)) q S)
    (hv : h (.inr ⟨q,v⟩)≠0) :
    v=qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e ∨
      v=qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e := by
  have hi := supported_incidence S _ h hh (.inr ⟨q,v⟩) hv
  change decide (∃ heq : q=q,
    heq ▸ v=qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e ∨
    heq ▸ v=qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e)=true at hi
  obtain ⟨heq,hv⟩ := of_decide_eq_true hi
  have hproof : heq=rfl := Subsingleton.elim _ _
  rw [hproof] at hv
  exact hv
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
