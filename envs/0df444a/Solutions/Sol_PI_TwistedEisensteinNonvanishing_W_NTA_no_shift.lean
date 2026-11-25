-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.no_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:20.937443+00:00
-- url     : https://prove2.me/submissions/d6de3ae4-a9e9-4fa6-a31d-ec22dec88fe5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iMul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iNat
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iPow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_not_int_inv_q

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
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) (d : ℕ) {w w' : E} (hw : w ≠ 0) (hwi : IntAt P w⁻¹)
    (hw' : IntAt P w') (h : w = (qOf P : E) ^ (d + 1) * w') : False := by
  have hq0 := q_ne P hp
  have hw'0 : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw h
  have hint : IntAt P (w⁻¹ * w' * (qOf P : E) ^ d) :=
    iMul P (iMul P hwi hw') (iPow P (iNat P _) d)
  have e : w⁻¹ * w' * (qOf P : E) ^ d = (qOf P : E)⁻¹ := by
    rw [h]
    field_simp
    ring
  rw [e] at hint
  exact not_int_inv_q P hp hint
end PI.TwistedEisensteinNonvanishing.W.NTA
