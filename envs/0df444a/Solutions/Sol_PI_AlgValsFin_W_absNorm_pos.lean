-- Prove2me | solution 1 for PI.AlgValsFin.W.absNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:26.682153+00:00
-- url     : https://prove2.me/submissions/21e7c461-1f07-4c68-93c9-6ce5546b5335

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FactorOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h
end PI.AlgValsFin.W
