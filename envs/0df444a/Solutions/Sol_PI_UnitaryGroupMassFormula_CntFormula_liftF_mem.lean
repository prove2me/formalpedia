-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.liftF_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:53.017509+00:00
-- url     : https://prove2.me/submissions/f567967d-e19a-4d05-8b6a-afc56164351b

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
theorem _root_.solution (c : 𝓀[F]) : liftF F c ∈ 𝒪[F] :=
  (IsLocalRing.residue_surjective c).choose.2
end PI.UnitaryGroupMassFormula.CntFormula
