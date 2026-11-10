-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.region_restrict_extend_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:51:26.100669+00:00
-- url     : https://prove2.me/submissions/1c209369-9925-41c7-bd5c-ce5d4172f88d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution {A : Type} [Fintype A] [DecidableEq A]
    (Y Z : Finset A) (h : Disjoint Y Z) (f : Word BDL26Field (LocalRegionIndex Y)) :
    restrictWordLinear Z (extendWordLinear Y f) = 0 := by
  funext p
  change extendLocalSignal Y f p.1 = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  exact Finset.disjoint_left.mp h hp p.2
end QEC.Coding.BDL26RXDecoderAdapter
