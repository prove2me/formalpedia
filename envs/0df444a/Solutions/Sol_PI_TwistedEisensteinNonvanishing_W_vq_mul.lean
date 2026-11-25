-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.vq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:58.367065+00:00
-- url     : https://prove2.me/submissions/f2d8073c-3c04-46a8-a90b-e70f31de02cf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unitAt_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_spec
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_eq

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
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
include hN hp hq
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) : vq P (a * b) = vq P a + vq P b := by
  obtain ⟨w, h1, hw⟩ := vq_spec hN hp hq ha
  obtain ⟨w', h2, hw'⟩ := vq_spec hN hp hq hb
  apply vq_eq hN hp hq _ (unitAt_mul hw hw')
  rw [zpow_add₀ (qE_ne P hp)]
  conv_lhs => rw [h1, h2]
  ring
end PI.TwistedEisensteinNonvanishing.W
