-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePointCount_det_gram_eq_sq_b3d628168b4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:22.423913+00:00
-- url     : https://prove2.me/submissions/f58e1a51-ab6d-4205-a040-775ab3513260

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq

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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount
namespace GroundTheory.Heights₂.Heights.LatticePointCount
theorem _root_.solution {r : ℕ} (c : Fin r → EuclideanSpace ℝ (Fin r)) :
    (Matrix.of fun i j ↦ @inner ℝ _ _ (c i) (c j)).det =
      ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c) ^ 2 := by
  have h := Matrix.gram_eq_conjTranspose_mul (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin r) ℝ) c
  change (Matrix.gram ℝ c).det = _
  rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply, sq]
  simp only [star_trivial]
  have hm : (Matrix.of fun i j => ((EuclideanSpace.basisFun (Fin r) ℝ).repr (c j)).ofLp i) =
      (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.toMatrix c := by
    ext i j
    simp [Basis.toMatrix_apply]
  rw [hm]
end GroundTheory.Heights₂.Heights.LatticePointCount
