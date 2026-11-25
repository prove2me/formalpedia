-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.ia_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:35.883974+00:00
-- url     : https://prove2.me/submissions/109bf7f0-04d6-431a-81bd-633e441113e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_zero
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
theorem _root_.solution (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a : E) :
    ∃ g : ℕ, IntAt P ((qOf P : E) ^ g * a) := by
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, mul_zero]; exact ia_zero P⟩
  obtain ⟨e, w, rfl, -, hw, -⟩ := hN.2.2.1 E P hp hq a ha
  refine ⟨(-e).toNat, ?_⟩
  have hq0 := qE_ne P hp
  have : (qOf P : E) ^ (-e).toNat * ((qOf P : E) ^ e * w) =
      (qOf P : E) ^ (((-e).toNat : ℤ) + e).toNat * w := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hq0, ← zpow_natCast]
    congr 2
    omega
  rw [this]
  exact ia_mul P (ia_qpow P _) hw
end PI.TwistedEisensteinNonvanishing.W
