-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:27.772014+00:00
-- url     : https://prove2.me/submissions/96b17464-2f78-4e70-bb1e-a7d357935b3f

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
theorem _root_.solution {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} [Fintype ι] (u : ι → Fin n → K) :
    gramAt h σ u = (colMatrix σ u)ᴴ * h * colMatrix σ u := by
  ext a b
  simp only [gramAt, embVec, colMatrix, Matrix.mul_apply, dotProduct, mulVec,
    conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end GroundTheory.Heights₂.Heights.KLinesGramChange
