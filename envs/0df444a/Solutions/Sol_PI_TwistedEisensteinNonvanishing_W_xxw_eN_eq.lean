-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.xxw_eN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:35.686329+00:00
-- url     : https://prove2.me/submissions/5c35887f-2b4e-45e1-81ad-6aa219e55b78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible

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
theorem _root_.solution {N : ℕ} (s : Fin N) : eN E N s.1 = Pi.single s 1 := by
  funext l
  simp only [eN, Pi.single_apply]
  by_cases h : l = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Fin.ext h')
end PI.TwistedEisensteinNonvanishing.W
