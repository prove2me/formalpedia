-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sum_vals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:02.204057+00:00
-- url     : https://prove2.me/submissions/7139306b-2981-4fc1-8b14-905ce77f70b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne


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
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) (A B : ℕ) (φ : E → K) :
    ∑ u ∈ valsQ E (qOf P) A B, φ u = Sg P A B φ := by
  classical
  have hq := pow_ne_zero A (qE_ne P hp)
  unfold valsQ Sg
  rw [Finset.sum_image]
  intro x _ y _ hxy
  have h2 : ((x : ℕ) : E) = y := by
    have := congrArg (· * (qOf P : E) ^ A) hxy
    simpa [div_mul_cancel₀ _ hq] using this
  exact_mod_cast h2
end PI.TwistedEisensteinNonvanishing.W
