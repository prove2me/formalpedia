-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rzLocalParity_sum_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:51:24.230529+00:00
-- url     : https://prove2.me/submissions/487d6adc-f892-4235-a52e-018457b34def

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_parityBit_weight_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_HammingWeight_sigma
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
section Fibers
variable {Label Coordinate : Type} [Fintype Label] [Fintype Coordinate]
  [DecidableEq Label] [DecidableEq Coordinate]
end Fibers
private theorem sigmaParity_sum_weight_le
    {Label : Type} [Fintype Label] {Coordinate : Label → Type}
    [∀ label, Fintype (Coordinate label)]
    (syndrome : Word Field (Sigma Coordinate)) :
    (∑ label : Label, HammingWeight
      (parityBit (fun coordinate : Coordinate label => syndrome ⟨label, coordinate⟩))) ≤
      HammingWeight syndrome := by
  calc
    _ ≤ ∑ label : Label, HammingWeight
        (fun coordinate : Coordinate label => syndrome ⟨label, coordinate⟩) := by
      apply Finset.sum_le_sum
      intro label _
      exact parityBit_weight_le _
    _ = HammingWeight syndrome := (HammingWeight_sigma syndrome).symm
private theorem sigmaParity_sum_weight_le_with_total
    {Label : Type} [Fintype Label] {Coordinate : Label → Type}
    [∀ label, Fintype (Coordinate label)] [total : Fintype (Sigma Coordinate)]
    (syndrome : Word Field (Sigma Coordinate)) :
    (∑ label : Label, HammingWeight
      (parityBit (fun coordinate : Coordinate label => syndrome ⟨label, coordinate⟩))) ≤
      HammingWeight syndrome := by
  let standard : Fintype (Sigma Coordinate) := Sigma.instFintype
  have ht : total = standard := Subsingleton.elim _ _
  have hw : @HammingWeight Field (Sigma Coordinate) _ _ total syndrome =
      @HammingWeight Field (Sigma Coordinate) _ _ standard syndrome :=
    congrArg (fun inst : Fintype (Sigma Coordinate) =>
      @HammingWeight Field (Sigma Coordinate) _ _ inst syndrome) ht
  exact (sigmaParity_sum_weight_le syndrome).trans_eq hw.symm
end QEC.Coding.BDL26ReplacementSupport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution
    (P : TannerSquarePresentation) (S : OddScale)
    (syndrome : Word Field (RZZ P S)) :
    (∑ z : P.Z, HammingWeight
      (parityBit (fun vertex : ZDoubleCylinderVertex P z S => syndrome ⟨z, vertex⟩))) ≤
      HammingWeight syndrome := by
  exact @sigmaParity_sum_weight_le_with_total P.Z inferInstance
    (fun z => ZDoubleCylinderVertex P z S) (fun z => inferInstance)
    (inferInstance : Fintype (RZZ P S)) syndrome
end QEC.Coding.BDL26ReplacementSupport
