-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__toySData_Del_d736ddffa61e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:35.857883+00:00
-- url     : https://prove2.me/submissions/557016b7-7471-4573-9f28-87643010f88a

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct

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
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E)
variable {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)
variable {sig hc}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    (toySData sig hc Del hDel hgap hlet loc).Del = Del := rfl
end Formalism.BasicNotions.Examples₂
