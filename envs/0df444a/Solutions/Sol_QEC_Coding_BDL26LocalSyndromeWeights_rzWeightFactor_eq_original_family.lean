-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.rzWeightFactor_eq_original_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:56:49.509198+00:00
-- url     : https://prove2.me/submissions/e62a49fd-7cdd-4ae5-a57e-f32662ab84d4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberFactor_eq_image

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (A : Finset (Word Bit (RZFiber P S z))) (t : ℝ) :
    rzWeightFactor P S z A t =
      weightedFamily (A.image (fiberExtend (rzSyndromeOwner P S) z)) t :=
  fiberFactor_eq_image _ _ A t
end QEC.Coding.BDL26LocalSyndromeWeights
