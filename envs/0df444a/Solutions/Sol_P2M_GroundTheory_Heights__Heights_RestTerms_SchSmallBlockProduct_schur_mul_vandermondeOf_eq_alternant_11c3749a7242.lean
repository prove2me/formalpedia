-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_schur_mul_vandermondeOf_eq_alternant_11c3749a7242
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:22.795721+00:00
-- url     : https://prove2.me/submissions/fec9875e-d7b3-4aa9-9c1d-929457983612

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSmallBlockProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchSmallBlockProduct
theorem _root_.solution {m : ℕ} (lam : Fin m → ℕ) :
    schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun i : Fin m => lam i + (m - 1 - (i : ℕ))) := by
  rw [← Schur.det_pow_add_staircase_eq, alternant, ← Matrix.det_transpose]
  rfl
end SchSmallBlockProduct
end GroundTheory.Heights₂.Heights.RestTerms
