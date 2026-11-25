-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.ia_div_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:43.121866+00:00
-- url     : https://prove2.me/submissions/7f4cf786-d289-46fc-9e93-3859196d62fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_qpow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne

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
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) {b b' : ℕ} (hb : b' ≤ b) {x : E}
    (hx : IntAt P (x / (qOf P : E) ^ b)) : IntAt P (x / (qOf P : E) ^ b') := by
  have e : x / (qOf P : E) ^ b' = (qOf P : E) ^ (b - b') * (x / (qOf P : E) ^ b) := by
    have hq := qE_ne P hp
    field_simp
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]
  rw [e]
  exact ia_mul P (ia_qpow P _) hx
end PI.TwistedEisensteinNonvanishing.W
