-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__star_isIntegral_8bceb60418dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:30:37.319811+00:00
-- url     : https://prove2.me/submissions/850b54bc-d5af-4d68-ab05-28d7c881fbfc

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField
open scoped TensorProduct
open IsDedekindDomain
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd E).toIntAlgHom
end Formalism.BasicNotions.Examples₂
