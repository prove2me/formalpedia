-- Prove2me | solution 1 for PI.TransInvLatW.shift_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:53.056048+00:00
-- url     : https://prove2.me/submissions/d7978ee2-0365-4c2b-855c-b23e3321c00a

import Definitions.Def_Formalism_PeriodIntegrals_TransInvLat
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TranslationInvariantLattice_TransInvLatOfPhase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical Complex
open PI PI.TransInvLatW
namespace PI.TransInvLatW
theorem _root_.solution (P A : ℂ) (G : ℂ → ℂ) (x y X Y : ℂ)
    (hy : ∀ z, G (z + y) * exp (-P * z * Y / A - P * y * Y / (2 * A)) = G z)
    (hph : exp (P * (x * Y - y * X) / (2 * A)) = 1) (z : ℂ) :
    G (z + (x + y)) * exp (-P * z * (X + Y) / A - P * (x + y) * (X + Y) / (2 * A)) =
      G (z + x) * exp (-P * z * X / A - P * x * X / (2 * A)) := by
  have h1 := hy (z + x)
  have hz : z + (x + y) = z + x + y := by ring
  rw [hz, ← h1, mul_assoc (G (z + x + y)), ← Complex.exp_add]
  congr 1
  have hE : -P * z * (X + Y) / A - P * (x + y) * (X + Y) / (2 * A) =
      (-P * (z + x) * Y / A - P * y * Y / (2 * A) + (-P * z * X / A - P * x * X / (2 * A))) +
        P * (x * Y - y * X) / (2 * A) := by ring
  rw [hE, Complex.exp_add, hph, mul_one]
end PI.TransInvLatW
