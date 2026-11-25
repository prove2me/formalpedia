-- Prove2me | solution 1 for PI.KerIso.FourSqW.trace_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:30.971006+00:00
-- url     : https://prove2.me/submissions/d6c030b8-861c-49a0-a507-b7d1fe7eb22b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Theorems.Thm_PI_KerIso_FourSqW_conjK_apply

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
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (z : E) :
    algebraMap K E (Algebra.trace K E (cj z)) = cj (algebraMap K E (Algebra.trace K E z)) := by
  have he : (algebraMap K E).comp (conjK cj hc : K →+* K) = (cj.toRingEquiv : E →+* E).comp (algebraMap K E) := by
    ext k
    simp only [RingHom.comp_apply, RingHom.coe_coe, conjK_apply, conjFun_spec]
    rfl
  have h1 := Algebra.trace_eq_of_equiv_equiv (conjK cj hc) cj.toRingEquiv he z
  have h2 : conjK cj hc (Algebra.trace K E z) = Algebra.trace K E (cj z) := by
    rw [h1, RingEquiv.apply_symm_apply]
    rfl
  rw [← h2, conjK_apply, conjFun_spec]
end PI.KerIso.FourSqW
