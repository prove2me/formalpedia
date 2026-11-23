-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.not_int_inv_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:30.111342+00:00
-- url     : https://prove2.me/submissions/f25404bb-664e-44fc-83a4-596bcb7f2ee2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_qO_mem
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne

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
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open PI.TwistedEisensteinNonvanishing.W.NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwistedEisensteinNonvanishing.W.NTA
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) : ¬ IntAt P ((qOf P : E)⁻¹) := by
  rintro ⟨r, s, hs, h⟩
  apply hs
  have hq := q_ne P hp
  have e : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E)) := by
    rw [map_mul, ← h, map_natCast, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  rw [IsFractionRing.injective (𝓞 E) E e]
  exact Ideal.mul_mem_left _ _ (qO_mem P)
end PI.TwistedEisensteinNonvanishing.W.NTA
