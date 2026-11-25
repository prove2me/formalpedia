-- Prove2me | solution 1 for PI.AlgValsFin.W.card_units_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:09.059057+00:00
-- url     : https://prove2.me/submissions/bd6318ac-b798-4235-9b26-b24f1e357fb1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace PI.AlgValsFin.W
theorem _root_.solution (n : ℕ) : 0 < Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal ^ n) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n v.ne_bot)
  exact Nat.card_pos
end PI.AlgValsFin.W
