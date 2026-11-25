-- Prove2me | solution 1 for PI.KLW.trace_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:02.668146+00:00
-- url     : https://prove2.me/submissions/52f72c1f-256b-454a-88ef-88e4ada55590

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (s t : ℕ) (x y : E) :
    Algebra.trace K E (((s : E) * x) * cj ((t : E) * y)) =
      ((s * t : ℕ) : K) * Algebra.trace K E (x * cj y) := by
  have e : ((s : E) * x) * cj ((t : E) * y) = algebraMap K E ((s * t : ℕ) : K) * (x * cj y) := by
    rw [map_mul cj, map_natCast cj, map_natCast]; push_cast; ring
  rw [e, ← Algebra.smul_def, map_smul, smul_eq_mul]
end PI.KLW
