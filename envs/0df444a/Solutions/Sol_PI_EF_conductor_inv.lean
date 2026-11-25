-- Prove2me | solution 1 for PI.EF.conductor_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:35.96673+00:00
-- url     : https://prove2.me/submissions/08451d21-fe65-416a-ae1f-f7d7e5f24b53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Theorems.Thm_PI_EF_factorsThrough_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ}
namespace PI.EF
theorem _root_.solution (χ : DirichletCharacter ℂ N) : (χ⁻¹).conductor = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  simp only [DirichletCharacter.conductorSet, Set.mem_setOf_eq]
  exact ⟨fun h => by simpa using factorsThrough_inv h, factorsThrough_inv⟩
end PI.EF
