-- Prove2me | solution 1 for SupLatW.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:22.743339+00:00
-- url     : https://prove2.me/submissions/2f0cb45f-ff83-4c26-a35d-1cedf3bc15cf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
import Theorems.Thm_SupLatW_supLat_eq_iff
import Theorems.Thm_SupLatW_covBy_supLat
import Theorems.Thm_SupLatW_eq_supLat_of_covBy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SupLatW
open Formalism.MainNotions.Ext.CutC
namespace SupLatW
theorem _root_.solution : SupLatLine := by
  intro R K _ _ _ _ _ _ ϖ hϖ r
  refine ⟨fun x hx => ?_, fun x y hx _ => supLat_eq_iff hϖ x y hx,
    fun M hle hM => eq_supLat_of_covBy hϖ M ((covBy_iff_quot_is_simple hle).mpr hM)⟩
  exact (covBy_iff_quot_is_simple le_sup_left).mp (covBy_supLat hϖ x hx)
end SupLatW
