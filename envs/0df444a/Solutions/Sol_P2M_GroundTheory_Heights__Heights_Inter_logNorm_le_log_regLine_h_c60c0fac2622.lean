-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_logNorm_le_log_regLine_h_c60c0fac2622
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:30:31.033635+00:00
-- url     : https://prove2.me/submissions/fd512149-1f59-4571-90f1-54990ac5dbef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_logNorm_eq_log_secNorm_66b2fbd2f820
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by
  rw [log_regLine_h, logNorm_eq_log_secNorm]
  have hpos : 0 < secNorm E t z := div_pos (norm_pos_iff.mpr ht0) (E.pos z hz)
  have h2 : Real.log (secNorm E t z) = Real.log (secNorm E t z ^ 2) / 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) (by norm_num)
end GroundTheory.Heights₂.Heights.Inter
