-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.map2_auxiliary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:57:50.180076+00:00
-- url     : https://prove2.me/submissions/39ea1d65-a022-4ff2-8abb-fbe8d4186924

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field P.Z) (p : RX2 P S) (hp : p ∉ zSector P S) :
    rxMap2Coord P S w p = 0 := by
  rcases p with (⟨x,f⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · rfl
  · rfl
  · exact (hp ((mem_zSector P S _).mpr ⟨z,rfl⟩)).elim
end QEC.Coding.BDL26RXDecoderAdapter
