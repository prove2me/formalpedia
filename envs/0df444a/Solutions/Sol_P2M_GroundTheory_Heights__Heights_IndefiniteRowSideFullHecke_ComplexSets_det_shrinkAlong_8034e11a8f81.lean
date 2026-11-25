-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_shrinkAlong_8034e11a8f81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:29.470695+00:00
-- url     : https://prove2.me/submissions/9873c829-9707-4114-b9c5-5a8f8aded9d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_shrinkAlong_apply_d4636c48fe45

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (i0 : ι) (k : ι → ℝ) (δ : ℝ) :
    LinearMap.det (shrinkAlong i0 k δ) = 1 - (1 - δ) * k i0 := by
  rw [← LinearMap.det_toMatrix']
  have hM : LinearMap.toMatrix' (shrinkAlong i0 k δ) =
      1 + Matrix.replicateCol Unit (-(1 - δ) • k) * Matrix.replicateRow Unit (Pi.single i0 (1 : ℝ)) := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, shrinkAlong_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]
    by_cases hij : i = j <;> by_cases hj : j = i0 <;> simp [hij, hj, eq_comm (a := i0)] <;> ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
