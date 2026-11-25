-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unitAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:13.677191+00:00
-- url     : https://prove2.me/submissions/37121118-0b99-42a4-8a29-cdff88d80f03

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_one

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
theorem _root_.solution : UnitAt P (1 : E) := ⟨one_ne_zero, ia_one P, by rw [inv_one]; exact ia_one P⟩
end PI.TwistedEisensteinNonvanishing.W
