-- Prove2me | solution 1 for PI.Mk.good_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:51.358795+00:00
-- url     : https://prove2.me/submissions/27e706ba-28f8-4b23-82eb-fe4982a2980d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution (ℓ : ℕ) : Good ℓ 1 :=
  ⟨monic_one, 0, by simp, by simp [nextCoeff], fun _ => by simp⟩
end PI.Mk
