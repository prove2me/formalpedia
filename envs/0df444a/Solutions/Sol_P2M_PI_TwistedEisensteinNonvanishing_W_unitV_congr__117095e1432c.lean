-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_unitV_congr__117095e1432c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:56.442938+00:00
-- url     : https://prove2.me/submissions/3ecc82aa-8cd3-46f2-bbd3-b301f5b14131

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
theorem _root_.solution (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) :
    unitV ξ a = unitV ξ b := by
  unfold unitV
  by_cases ha : IsUnit (redP P a)
  · have hb : IsUnit (redP P b) := h ▸ ha
    rw [dif_pos ha, dif_pos hb, show ha.unit = hb.unit from Units.ext h]
  · rw [dif_neg ha, dif_neg (h ▸ ha)]
end PI.TwistedEisensteinNonvanishing.W
