-- Prove2me | solution 1 for QEC.Coding.BDL26LocalSyndromeWeights.fiberExtend_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:11:48.775476+00:00
-- url     : https://prove2.me/submissions/05ce457a-fdbf-4af1-9432-371bf032135e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_fiberExtend_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical
namespace QEC.Coding.BDL26LocalSyndromeWeights
theorem _root_.solution {C Label : Type*} (owner : C → Label) (label : Label) :
    Function.Injective (fiberExtend owner label) := by
  intro x y h
  funext c
  have he := congrFun h c.val
  rw [fiberExtend_apply owner label x c.val c.property,
    fiberExtend_apply owner label y c.val c.property] at he
  exact he
end QEC.Coding.BDL26LocalSyndromeWeights
