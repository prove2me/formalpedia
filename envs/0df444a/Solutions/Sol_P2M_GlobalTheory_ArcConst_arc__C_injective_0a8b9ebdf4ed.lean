-- Prove2me | solution 1 for P2M_GlobalTheory_ArcConst_arc__C_injective_0a8b9ebdf4ed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:59.570446+00:00
-- url     : https://prove2.me/submissions/3f6a6f61-e527-474b-b472-05e1c32a545e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_isDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.ArcConst
theorem _root_.solution (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective ((arcι Dw K).comp (PowerSeries.C (R := K))) :=
  have := isDomain Dw K
  RingHom.injective _
end GlobalTheory.ArcConst
