-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:28.2848+00:00
-- url     : https://prove2.me/submissions/c2337a3b-92a5-4c3c-832f-16f3dd2aaaa8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramPosDef

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
open GroundTheory.Heights₂.Heights.KLinesGramPosDef
open Matrix
variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}
namespace GroundTheory.Heights₂.Heights.KLinesGramPosDef
theorem _root_.solution (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (u : ι → Fin n → K) :
    gramAt h σ u = (((Matrix.of fun j a => u a j).map σ)ᴴ * h *
      (Matrix.of fun j a => u a j).map σ) := by
  ext a b
  simp [gramAt, embVec, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
end GroundTheory.Heights₂.Heights.KLinesGramPosDef
