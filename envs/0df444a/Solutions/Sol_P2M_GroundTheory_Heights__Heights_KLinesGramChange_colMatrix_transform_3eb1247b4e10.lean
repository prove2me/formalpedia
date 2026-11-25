-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGramChange_colMatrix_transform_3eb1247b4e10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:48.265859+00:00
-- url     : https://prove2.me/submissions/c5aa4ded-3d4d-4094-bd76-2ca22de31fc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramChange

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
open Matrix
open GroundTheory.Heights₂.Heights.KLinesGramChange
namespace GroundTheory.Heights₂.Heights.KLinesGramChange
theorem _root_.solution {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (P : Matrix ι ι K) :
    colMatrix σ (fun a => ∑ b, P b a • u b) = colMatrix σ u * P.map σ := by
  ext j a
  simp only [colMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
end GroundTheory.Heights₂.Heights.KLinesGramChange
