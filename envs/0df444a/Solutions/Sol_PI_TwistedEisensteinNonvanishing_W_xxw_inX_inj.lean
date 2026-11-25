-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.xxw_inX_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:26.058339+00:00
-- url     : https://prove2.me/submissions/7cb06063-559e-4f1d-8caf-d6ee00ba5cda

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
theorem _root_.solution {n c : ℕ} {v w : Fin n → E} (h : inX E n c v = inX E n c w) : v = w := by
  funext p
  have h1 := congrFun h (Fin.castAdd c p)
  simpa [inX, LinearMap.pi_apply, Fin.coe_castAdd, p.isLt] using h1
end PI.TwistedEisensteinNonvanishing.W
