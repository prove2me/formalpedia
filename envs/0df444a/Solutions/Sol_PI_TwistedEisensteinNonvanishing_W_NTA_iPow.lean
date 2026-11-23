-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.iPow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:01.941049+00:00
-- url     : https://prove2.me/submissions/b1f6c3e2-2d75-45f0-8684-77b66f06b549

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iMul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iNat

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
theorem _root_.solution {a : E} (ha : IntAt P a) (m : ℕ) : IntAt P (a ^ m) := by
  induction m with
  | zero => simpa using iNat P 1
  | succ m ih => rw [pow_succ]; exact iMul P ih ha
end PI.TwistedEisensteinNonvanishing.W.NTA
