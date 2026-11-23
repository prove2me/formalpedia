-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__toySData_HH_645ede68cc2d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:31.84548+00:00
-- url     : https://prove2.me/submissions/513b02d4-7d6e-4588-825b-2921e0dd4008

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



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
    Module.finrank ℂ (toySData sig hc Del hDel hgap hlet loc).HH = 0 := by
  show Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) = 0
  simp
end Formalism.BasicNotions.Examples₂
