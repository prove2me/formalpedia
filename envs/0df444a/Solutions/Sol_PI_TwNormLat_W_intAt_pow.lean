-- Prove2me | solution 1 for PI.TwNormLat.W.intAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:27.65684+00:00
-- url     : https://prove2.me/submissions/32632853-530d-4bae-a011-e881fa3154d4

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_PI_TwNormLat_W_intAt_one
import Theorems.Thm_PI_TwNormLat_W_intAt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution {a : E} (ha : IntAt P a) (k : ℕ) : IntAt P (a ^ k) := by
  induction k with
  | zero => simpa using PI.TwNormLat.W.intAt_one P
  | succ k ih =>
    rw [pow_succ]
    exact PI.TwNormLat.W.intAt_mul P ih ha
end PI.TwNormLat.W
