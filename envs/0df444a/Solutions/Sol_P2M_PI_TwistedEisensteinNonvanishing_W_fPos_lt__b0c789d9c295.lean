-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_fPos_lt__b0c789d9c295
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:35.62992+00:00
-- url     : https://prove2.me/submissions/51da65ed-2d48-47cb-8f1b-3b299fadea7a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity

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
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {k₀ c n l : ℕ} (_hk : k₀ ≤ n) (hl : l < n + c) : fPos k₀ c n l < n + c := by
  unfold fPos
  split_ifs <;> omega
end PI.TwistedEisensteinNonvanishing.W
