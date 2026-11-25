-- Prove2me | solution 1 for PI.KLW.splitK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:56.691991+00:00
-- url     : https://prove2.me/submissions/0322a483-6aaf-4b41-8cb6-e2b05b5cb5c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Theorems.Thm_PI_KLW_conjK_spec

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
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {p : ℕ}
    (hs : PI.KerIso.SplitsAt K cj p) : SplitK (conjK cj hc.2.1) p := by
  obtain ⟨P, hP, hpP, a, b, hab, ha, hb⟩ := hs
  exact ⟨P, hP, hpP, a, b, (algebraMap K E).injective (by rw [conjK_spec, hab]), ha, hb⟩
end PI.KLW
