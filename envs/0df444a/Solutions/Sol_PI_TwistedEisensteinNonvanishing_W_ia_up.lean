-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.ia_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:42.82848+00:00
-- url     : https://prove2.me/submissions/2ddd3980-2600-4577-8d3f-d0a2495474df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_qpow

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
theorem _root_.solution {j D : ℕ} (hjD : j ≤ D) {z : E} (hz : IntAt P ((qOf P : E) ^ j * z)) :
    IntAt P ((qOf P : E) ^ D * z) := by
  have e : (qOf P : E) ^ D * z = (qOf P : E) ^ (D - j) * ((qOf P : E) ^ j * z) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD]
  rw [e]
  exact ia_mul P (ia_qpow P _) hz
end PI.TwistedEisensteinNonvanishing.W
