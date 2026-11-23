-- Prove2me | solution 1 for PI.EF.Lent_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:11.545851+00:00
-- url     : https://prove2.me/submissions/09c282a6-15b2-4d4b-9233-0759df53d193

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_Lent_one_apply

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
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ =ᶠ[𝓝 s] (fun z => z - 1) * LFunction χ := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  rw [Lent_one_apply h hz]
  rfl
end PI.EF
