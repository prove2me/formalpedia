-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.rz_extend_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:08:09.0132+00:00
-- url     : https://prove2.me/submissions/64c16b70-ff88-4946-b834-5cd9e4fc17e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_weight

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (x : Word Bit (RZFiber P S z)) :
    HammingWeight (fiberExtend (rzSyndromeOwner P S) z x) = HammingWeight x := by
  convert fiberExtend_weight (rzSyndromeOwner P S) z x using 1 <;>
    congr 1 <;> exact Subsingleton.elim _ _
end QEC.Coding.BDL26LocalSyndromeWeights
