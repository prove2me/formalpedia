-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unitAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:06.806541+00:00
-- url     : https://prove2.me/submissions/ad7471e0-b813-4804-adbd-cb1d358e457d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul

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
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
variable {P}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {w w' : E} (h : UnitAt P w) (h' : UnitAt P w') : UnitAt P (w * w') :=
  ⟨mul_ne_zero h.1 h'.1, ia_mul P h.2.1 h'.2.1, by rw [mul_inv]; exact ia_mul P h.2.2 h'.2.2⟩
end PI.TwistedEisensteinNonvanishing.W
