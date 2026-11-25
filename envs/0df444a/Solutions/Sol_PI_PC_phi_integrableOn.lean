-- Prove2me | solution 1 for PI.PC.phi_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:37.158256+00:00
-- url     : https://prove2.me/submissions/3a4c0219-5540-47d5-9e84-4e5c91e16aa6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution {p : ℝ} (q : ℝ) (hp : 2 ≤ p) : IntegrableOn phi (Icc p q) volume := by
  have h : IntegrableOn (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)) (Icc 2 q) volume :=
    Chebyshev.integrableOn_theta_div_id_mul_log_sq q
  exact h.mono_set (Icc_subset_Icc_left hp)
end PI.PC
