-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_fIdx_fPos__6ef873873a47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:36.463851+00:00
-- url     : https://prove2.me/submissions/231dfc2a-f1d1-4150-9839-68d6d1614ce5

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
theorem _root_.solution {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : fIdx k₀ c n (fPos k₀ c n l) = l := by
  unfold fIdx fPos
  split_ifs <;> omega
end PI.TwistedEisensteinNonvanishing.W
