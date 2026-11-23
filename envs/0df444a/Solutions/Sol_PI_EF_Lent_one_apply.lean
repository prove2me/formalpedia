-- Prove2me | solution 1 for PI.EF.Lent_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:47.664135+00:00
-- url     : https://prove2.me/submissions/4a76c9a3-f15b-4d97-96a7-6400a980af77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC

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
    Lent χ s = (s - 1) * LFunction χ s := by
  subst h
  unfold Lent
  rw [if_pos rfl]
  first
    | (rw [LFunctionTrivChar₁, Function.update_of_ne hs]; rfl)
    | (simp [LFunctionTrivChar₁, Function.update_of_ne hs])
    | (simp [LFunctionTrivChar₁, hs])
end PI.EF
