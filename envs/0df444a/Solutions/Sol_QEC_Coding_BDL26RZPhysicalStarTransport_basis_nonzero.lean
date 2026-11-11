-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.basis_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:34:15.072628+00:00
-- url     : https://prove2.me/submissions/9ba293f1-0c91-4953-b814-8171cd659b89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution {I : Type} (q : I) :
    canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ≠ (0 : Word BDL26FiniteTannerSquare.Field I) := by
  intro hz
  have hself : canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q q=(1 : BDL26FiniteTannerSquare.Field) := by
    change Pi.single (M := fun _ : I => BDL26FiniteTannerSquare.Field) q (1 : BDL26FiniteTannerSquare.Field) q=1
    exact Pi.single_eq_same (M := fun _ : I => BDL26FiniteTannerSquare.Field) q (1 : BDL26FiniteTannerSquare.Field)
  have hzero : (0 : Word BDL26FiniteTannerSquare.Field I) q=(0 : BDL26FiniteTannerSquare.Field) := rfl
  exact one_ne_zero (hself.symm.trans ((congrFun hz q).trans hzero))
end QEC.Coding.BDL26RZPhysicalStarTransport
