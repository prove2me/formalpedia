-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_fd8121b8213d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:23.274287+00:00
-- url     : https://prove2.me/submissions/967aa53f-5880-4b76-afb3-6d3109fcc66c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_powMatrix_eq_mul_d892086046d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_hMatrix_staircase_8f257c117f9e

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
theorem _root_.solution (lam : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (lam i + (m - 1 - (i : ℕ)))).det =
      schur (Fin m) lam *
        (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (m - 1 - (i : ℕ))).det := by
  rw [powMatrix_eq_mul, powMatrix_eq_mul (fun i : Fin m => m - 1 - (i : ℕ)), Matrix.det_mul,
    Matrix.det_mul, det_hMatrix_staircase, one_mul]
  rw [schur]
  congr 2
  apply Matrix.ext
  intro i c
  simp only [hMatrix, Matrix.of_apply]
  congr 1
  have := i.isLt
  have := c.isLt
  push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + (c : ℕ) ≤ m by omega),
    Nat.cast_sub (show 1 + (i : ℕ) ≤ m by omega)]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Schur
