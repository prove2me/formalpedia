-- Prove2me | solution 1 for P2M_GlobalTheory_LocSpan_isIntegral__E_a7279f9601bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:28.590087+00:00
-- url     : https://prove2.me/submissions/6f3ebcb5-8313-474d-97f7-537146eb708d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocSpan
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
omit [StarRing E]
namespace GlobalTheory.LocSpan
theorem _root_.solution {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
    (x : 𝓞 E) : IsIntegral 𝒪[A.Fp] (A.ιE (x : E)) :=
  (x.isIntegral_coe.map A.ιE.toIntAlgHom).tower_top
end GlobalTheory.LocSpan
