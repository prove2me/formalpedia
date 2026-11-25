-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsAdmissible_nrmv_70a1134c823d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:06.733565+00:00
-- url     : https://prove2.me/submissions/d0808de5-fe5f-47d3-9e72-90ee70e2eed2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAENrm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_const_mul_b5306e01af29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_norm_ne_zero_0d8080cf190b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace IsAdmissible
theorem _root_.solution (h : HermNorm n) {Z : ProjCycle ℂ n} {v : Fin n → ℂ}
    (hv : IsAdmissible Z v) : IsAdmissible Z (nrmv h v) := by
  intro W hW hmem
  apply hv W hW
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hv W hW
    simp [linForm]
  have hc : ((h.norm v : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (h.norm_ne_zero hv0))
  have hmem' : C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v ∈ W := by
    rw [← linForm_const_mul]; exact hmem
  have : linForm v = C (((h.norm v : ℝ) : ℂ)⁻¹)⁻¹ * (C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [this]
  exact W.mul_mem_left _ hmem'
end IsAdmissible
end GroundTheory.Heights₂.Heights
