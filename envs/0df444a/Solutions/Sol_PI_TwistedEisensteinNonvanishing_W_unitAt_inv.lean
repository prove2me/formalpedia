-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unitAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:32.738823+00:00
-- url     : https://prove2.me/submissions/435194f5-6ea4-4c1e-903b-49469efe4702

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown

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
theorem _root_.solution {w : E} (h : UnitAt P w) : UnitAt P w⁻¹ := ⟨inv_ne_zero h.1, h.2.2, by rw [inv_inv]; exact h.2.1⟩
end PI.TwistedEisensteinNonvanishing.W
