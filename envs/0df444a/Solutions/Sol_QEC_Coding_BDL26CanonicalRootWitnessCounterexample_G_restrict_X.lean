-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.G_restrict_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:05:39.866074+00:00
-- url     : https://prove2.me/submissions/eb09fe15-e32f-4390-a0b6-6d927a119b99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_disjoint


set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).correctionRegion x) (G S) = 0 := by
  classical
  ext p
  change (∑ q, extendWordLinear ((LQ S).correctionRegion q) (localW S q)) p.val = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q _
  have hnot : p.val ∉ (LQ S).correctionRegion q := by
    intro hq
    have hxU : p.val ∈ correctionRegionUnion (LX S) :=
      Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, p.property⟩
    have hqU : p.val ∈ (A S).qCorrectionSector := by
      rw [(A S).qCorrectionSector_eq_regions]
      exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, hq⟩
    exact (Finset.disjoint_left.mp (A S).correction_sectors_disjoint) hxU hqU
  change (if h : p.val ∈ (LQ S).correctionRegion q then _ else 0) = 0
  rw [dif_neg hnot]
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
