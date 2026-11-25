-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.IsPD.entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:15.739999+00:00
-- url     : https://prove2.me/submissions/c19f09b8-f842-426a-b863-ac1b32cdebe4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
namespace IsPD
theorem _root_.solution {N : ℕ} (i j : Fin N) : IsPD (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) :=
  ⟨0, MvPolynomial.X (i, j), fun g => by simp [ent]⟩
end IsPD
end PI.UnitaryGroupMassFormula.PolyCoef
