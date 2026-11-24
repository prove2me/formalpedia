-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.gm_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:24.195439+00:00
-- url     : https://prove2.me/submissions/e083ac79-fc4c-4941-97ee-6ae56b4312df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (gm I γ).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (gm I γ).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := (mem_gf I γ).choose_spec.2
end PI.UnitaryGroupMassFormula.LCG
