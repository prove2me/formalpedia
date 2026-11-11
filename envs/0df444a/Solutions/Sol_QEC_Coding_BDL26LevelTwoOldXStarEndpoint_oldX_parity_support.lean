-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_parity_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:34:14.547205+00:00
-- url     : https://prove2.me/submissions/cc430b0f-ba35-4b3d-8d25-6bbb6f0c2f8a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_physical_star_subset
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_mem_physicalXStar
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_raw_star_cover
attribute [local simp] QEC.Coding.BDL26RXPhysicalStarTransport.mem_physicalXStar


section
noncomputable section
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
private theorem support_star_iff (B : TannerSquarePresentation)
    (qF : Fintype B.Q) (x : B.X) (h : Word F B.Q) :
    letI : Fintype B.Q := qF
    hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar B x ↔
      ∀ r, h r ≠ 0 → B.xq x r = true := by
  letI : Fintype B.Q := qF
  constructor
  · intro hs r hn
    have hm : r ∈ hammingSupport h :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    exact (BDL26RXPhysicalStarTransport.mem_physicalXStar B x r).mp (hs hm)
  · intro hs r hr
    exact (BDL26RXPhysicalStarTransport.mem_physicalXStar B x r).mpr
      (hs r (Finset.mem_filter.mp hr).2)
private theorem raw_oldX_qParity_support (B : TannerSquarePresentation)
    (A : TannerSquareAdmissible B) (S : OddScale) (x : B.X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (RZQ B S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (rzReplacementPresentation B A S) (Sum.inr (x,c))) :
    ∀ q, rzQParity B S h q≠0 →
      q∈BDL26RXPhysicalStarTransport.physicalXStar B x := by
  intro q hq
  by_contra hN
  have hz : ∀ v : QDoubleCylinderVertex (transposePresentation B) q S,
      h (Sum.inr ⟨q,v⟩)=0 := by
    intro v
    by_contra hn
    have hi := (support_star_iff (rzReplacementPresentation B A S)
      (nativeRZQFintype B S) (Sum.inr (x,c)) h).mp hh (Sum.inr ⟨q,v⟩) hn
    change rzXQIncidence B A S
      (Sum.inr (x,c)) (Sum.inr ⟨q,v⟩)=true at hi
    have hcover := BDL26RZPhysicalXStarTransport.raw_star_cover B A S
      (Sum.inr (x,c)) (Sum.inr ⟨q,v⟩) hi
    have hqmem : q∈BDL26RXPhysicalStarTransport.physicalXStar B x :=
      (BDL26RZFiniteBlockTransport.Coordinates.mem_input_q B S _ _ q v).mp hcover
    exact hN hqmem
  apply hq
  change (∑ v : QDoubleCylinderVertex (transposePresentation B) q S,
    h (Sum.inr ⟨q,v⟩))=0
  exact Finset.sum_eq_zero (fun v _ => hz v)
private theorem levelOne_oldX_qParity_neighborhood (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (RZQ (P S) S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (rzReplacementPresentation (P S)
        (rxState S baseState).admissible.toTannerSquareAdmissible S) (Sum.inr (x,c))) :
    ∀ q, rzQParity (P S) S h q≠0 → q∈Neighborhood S x.1 := by
  intro q hq
  exact physical_star_subset S x
    (raw_oldX_qParity_support (P S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S x c h hh q hq)
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
attribute [local instance] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldXActualQFintype
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint
theorem _root_.solution (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (C S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (C S) (Sum.inr (x,c))) :
    ∀ q, rzQParity (P S) S h q≠0 → q∈Neighborhood S x.1 := by
  apply levelOne_oldX_qParity_neighborhood S x c h
  apply (support_star_iff
    (rzReplacementPresentation (P S)
      (rxState S baseState).admissible.toTannerSquareAdmissible S)
    (nativeRZQFintype (P S) S) (Sum.inr (x,c)) h).mpr
  intro r hr
  have hi := (support_star_iff (C S) (oldXActualQFintype S)
    (Sum.inr (x,c)) h).mp hh r hr
  change rzXQIncidence (P S)
    (rxState S baseState).admissible.toTannerSquareAdmissible S
    (Sum.inr (x,c)) r=true at hi
  exact hi
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
