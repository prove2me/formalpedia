-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_powMatrix_eq_mul_d892086046d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:04.944521+00:00
-- url     : https://prove2.me/submissions/5e1357e1-74c6-4864-b50f-f3a35dcc73b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_sum_hsymm_mul_coeff_omitProduct_8c99bd9e1f3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (α : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ α i) =
      hMatrix α * omitProductCoeffMatrix m := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.of_apply]
  simp only [hMatrix, omitProductCoeffMatrix, Matrix.of_apply, completeSymmetric_natSub]
  rw [← sum_hsymm_mul_coeff_omitProduct j (α i), Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun c => (if m - 1 - c ≤ α i then hsymm (Fin m) ℚ (α i - (m - 1 - c))
    else 0) * PowerSeries.coeff (m - 1 - c) (omitProduct j)) m]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro c hc
  rw [mem_range] at hc
  rw [mul_comm]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
