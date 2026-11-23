-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.resF_liftF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:20.765607+00:00
-- url     : https://prove2.me/submissions/c1b6948e-2ea0-497d-99a6-4348f0156461

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution (c : 𝓀[F]) : resF F (liftF F c) = c := by
  rw [liftF, resF_coe]
  exact (IsLocalRing.residue_surjective c).choose_spec
end PI.UnitaryGroupMassFormula.CntFormula
