-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.resF_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:15.698306+00:00
-- url     : https://prove2.me/submissions/026e7736-4602-4c1e-abe9-fc425da9cd0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr

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
theorem _root_.solution (o : 𝒪[F]) : resF F (o : F) = IsLocalRing.residue 𝒪[F] o := by
  rw [resF, dif_pos o.2]
end PI.UnitaryGroupMassFormula.CntFormula
