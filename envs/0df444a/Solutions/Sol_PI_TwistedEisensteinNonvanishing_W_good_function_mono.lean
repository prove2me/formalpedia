-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.good_function_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:35.917906+00:00
-- url     : https://prove2.me/submissions/fdd8daf3-73bf-4fca-9a1e-254d407d9334

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_up


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
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a b a' : ℕ} (ha : a ≤ a') {φ : E → K} (h : Good1 P a b φ) : Good1 P a' b φ :=
  ⟨fun u hu => ia_up P ha (h.1 u hu), h.2⟩
end PI.TwistedEisensteinNonvanishing.W
