-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.resF_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:23.931165+00:00
-- url     : https://prove2.me/submissions/bcf1520a-c29c-43df-a878-8166c0a3480f

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
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resF F (ϖ : F) = 0 := by
  rw [resF_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hϖ.not_isUnit
end PI.UnitaryGroupMassFormula.CntFormula
