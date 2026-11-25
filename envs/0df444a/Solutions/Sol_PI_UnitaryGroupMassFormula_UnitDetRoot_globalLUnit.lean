-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:35.373952+00:00
-- url     : https://prove2.me/submissions/8e79305e-f486-43d4-9784-30e9686c4cca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobFin
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_globalLUnit_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_img
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_smul_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_std_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_std_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : GlobalLUnit :=
  globalLUnit_of
    (fun F _ _ _ _ _ c h => vol_smul_le F c h)
    (fun F _ _ _ δ Λ => vol_img F δ Λ)
    (fun _ _ _ _ _ _ _ _ _ _ _ hok => vol_std_le hok)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => vol_std_ne_bot)
end PI.UnitaryGroupMassFormula.UnitDetRoot
