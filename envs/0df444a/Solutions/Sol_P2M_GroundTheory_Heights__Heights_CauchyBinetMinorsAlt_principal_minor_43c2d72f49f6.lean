-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_principal_minor_43c2d72f49f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:23:42.795059+00:00
-- url     : https://prove2.me/submissions/5e81f8ec-fa95-48bf-be97-a4a3ea9d2b68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinet_proof_066722d63378


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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
namespace GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
theorem _root_.solution {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℂ)
    (S : {S : Finset (Fin q) // S.card = k}) :
    ((Mᴴ * M).submatrix (S.1.orderEmbOfFin S.2) (S.1.orderEmbOfFin S.2)).det =
      ∑ T : {T : Finset (Fin p) // T.card = k},
        ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, CauchyBinet.proof]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h1 : colsOf (Mᴴ.submatrix (S.1.orderEmbOfFin S.2) id) T =
      (M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2))ᴴ := by
    ext i j
    simp [colsOf, conjTranspose_apply]
  have h2 : rowsOf (M.submatrix id (S.1.orderEmbOfFin S.2)) T =
      M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2) := by
    ext i j
    simp [rowsOf]
  rw [h1, h2, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl
end GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
