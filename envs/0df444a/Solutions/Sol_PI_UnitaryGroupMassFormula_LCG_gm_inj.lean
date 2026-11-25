-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.gm_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:09.551519+00:00
-- url     : https://prove2.me/submissions/8d49f2c3-6bc7-4995-9dea-b5afb3c0993f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_gm_spec

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
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) {γ γ' : I.GFset} (h : gm I γ = gm I γ') : γ = γ' := by
  obtain ⟨h1a, h1b⟩ := gm_spec I γ
  obtain ⟨h2a, h2b⟩ := gm_spec I γ'
  rw [h] at h1a h1b
  apply Subtype.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1a v).trans (h2a v).symm))
  · exact Subtype.ext (Units.ext (h1b.trans h2b.symm))
end PI.UnitaryGroupMassFormula.LCG
