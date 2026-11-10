-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.z_correction_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:30:43.620258+00:00
-- url     : https://prove2.me/submissions/f17c71b2-f1ad-4ed3-b8f8-970833cbd48a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    (localZ P S).correctionRegion z = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have howner : rxCorrectionOwner P S p = Vertex.z z := (Finset.mem_filter.mp hp).2
  rcases p with ⟨x,e⟩ | ⟨q,v⟩ <;> cases howner
end QEC.Coding.BDL26RXDecoderAdapter
