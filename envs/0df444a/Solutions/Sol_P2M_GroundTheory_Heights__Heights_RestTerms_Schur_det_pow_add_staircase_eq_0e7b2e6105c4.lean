-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:36.573853+00:00
-- url     : https://prove2.me/submissions/ece6aaef-c64d-4840-b13b-e4b8a5875ac2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_fd8121b8213d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b

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
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution {m : ℕ} (lam : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (lam i + (m - 1 - (i : ℕ)))).det =
      schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) := by
  rw [det_pow_add_staircase, det_pow_staircase_eq_vandermondeOf]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
