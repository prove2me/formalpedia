-- Prove2me | solution 1 for QPK.prodSet_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:44.850425+00:00
-- url     : https://prove2.me/submissions/5a0f25f5-2912-43b1-95d8-02047716ab81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ProdSetIsClosed
import Theorems.Thm_QPK_prodSet_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
namespace QPK
theorem _root_.solution {N H : Set G} (hN : IsClosed N) (hH : IsCompact H) :
    IsClosed (prodSet N H) := by
  rw [prodSet_eq_mul]
  first
    | exact hN.mul_isCompact hH
    | exact IsClosed.mul_isCompact hN hH
    | exact hN.mul_right_of_isCompact hH
    | exact IsClosed.mul_right_of_isCompact hN hH
    | exact hN.mul_isCompact_right hH
    | exact (hN.smul_left_of_isCompact hH)
end QPK
