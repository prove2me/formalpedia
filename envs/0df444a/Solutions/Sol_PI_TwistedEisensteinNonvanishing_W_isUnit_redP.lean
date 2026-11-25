-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.isUnit_redP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:48.728658+00:00
-- url     : https://prove2.me/submissions/583725a7-22fe-4816-a414-25416bf59d32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_one__7aa5b9a9571c

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
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {w : E} (hw : UnitAt P w) : IsUnit (redP P w) := by
  obtain ⟨hw0, hi, hi'⟩ := hw
  have h := reduction_mul' P hi hi'
  rw [mul_inv_cancel₀ hw0, reduction_one'] at h
  exact IsUnit.of_mul_eq_one (b := redP P w⁻¹) h.symm
end PI.TwistedEisensteinNonvanishing.W
