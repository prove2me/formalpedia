-- Prove2me | solution 1 for PI.ArtSch.Glue.coeff_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:26.366517+00:00
-- url     : https://prove2.me/submissions/35969228-6a2a-44d7-873c-97ed1968546b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.ArtSch.Glue
theorem _root_.solution (x : OCb l) (n : ℕ) : ∀ k : ℕ,
    PreTilt.coeff (n + k) x ^ (l ^ k) = PreTilt.coeff n x
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', pow_mul, ← add_assoc, PreTilt.coeff_pow_p, solution x n k]
end PI.ArtSch.Glue
