-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.reduction_eq_zero_of_integral_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:27.946277+00:00
-- url     : https://prove2.me/submissions/5da382dc-913e-4d16-8051-89bdafdd2d43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_reduction_absNorm_mul_eq_zero
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne


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
theorem _root_.solution {z : E} (hp : (Ideal.absNorm P.asIdeal).Prime) (hz : IntAt P (z / (qOf P : E))) :
    redP P z = 0 := by
  have hq := NTA.q_ne (P := P) hp
  have e : z = (qOf P : E) * (z / (qOf P : E)) := by field_simp
  rw [e]
  exact reduction_absNorm_mul_eq_zero hz
end PI.TwistedEisensteinNonvanishing.W
