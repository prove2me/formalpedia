-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.reduction_absNorm_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:31.18742+00:00
-- url     : https://prove2.me/submissions/4c6912c3-b67f-449d-8bfd-d59fb60abbac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwChrOne_Pf_reduction_eq_zero


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
theorem _root_.solution {z : E} (hz : IntAt P z) : redP P ((qOf P : E) * z) = 0 := by
  obtain ⟨r, s, hs, hsz⟩ := hz
  refine PI.TwChrOne.Pf.reduction_eq_zero P (p := (Ideal.absNorm P.asIdeal : 𝓞 E)) (r := r) (s := s)
    (Ideal.absNorm_mem P.asIdeal) hs ?_
  rw [← hsz, map_natCast]
  unfold qOf
  ring
end PI.TwistedEisensteinNonvanishing.W
