-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.weighted_sum_to_gauss_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:20.311106+00:00
-- url     : https://prove2.me/submissions/a7ae4b8c-974c-4e7b-9ea7-7f2c27f0456d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum

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
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N : ℕ} {f g : E → K} {c : K} (h : W1 P N N f = c * W1 P N N g) :
    Sg P N N f = c * Sg P N N g := by
  have hq0 : ((qOf P : K) ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hK)
  unfold W1 at h
  apply mul_left_cancel₀ hq0
  rw [h]
  ring
end PI.TwistedEisensteinNonvanishing.W
