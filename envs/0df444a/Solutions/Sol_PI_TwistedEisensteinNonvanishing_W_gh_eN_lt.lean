-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.gh_eN_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:44.548469+00:00
-- url     : https://prove2.me/submissions/a8beec1b-d167-447f-9d4e-40dc4516102f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N s : ℕ} (h : s < N) : eN E N s = Pi.single (⟨s, h⟩ : Fin N) 1 := by
  funext l
  simp [eN, Pi.single_apply, Fin.ext_iff]
end PI.TwistedEisensteinNonvanishing.W
