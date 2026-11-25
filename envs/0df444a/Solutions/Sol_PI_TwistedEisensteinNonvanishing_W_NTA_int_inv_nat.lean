-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.int_inv_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:14.304929+00:00
-- url     : https://prove2.me/submissions/6ca2861e-6f46-4a90-8076-7b47cc71a35c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_natCast_notMem

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
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) : IntAt P ((m : E)⁻¹) := by
  have hm0 : (m : E) ≠ 0 := by
    have : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    exact_mod_cast this
  refine ⟨1, (m : 𝓞 E), natCast_notMem P hp hm, ?_⟩
  rw [map_natCast, map_one, mul_inv_cancel₀ hm0]
end PI.TwistedEisensteinNonvanishing.W.NTA
