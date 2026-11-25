-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_reduction_add__59831082df14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:03.454676+00:00
-- url     : https://prove2.me/submissions/7f7af418-637d-49d0-93cc-144c831e6ef2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_redP_sum__a67c2a3dc9b8

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
variable (P)
variable {P}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a + b) = redP P a + redP P b := by
  have h := redP_sum' (P := P) (Finset.univ : Finset (Fin 2)) ![a, b] (by intro i; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h
end PI.TwistedEisensteinNonvanishing.W
