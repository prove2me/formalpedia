-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_of_ne_zero_06f128ad0be1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:26.468987+00:00
-- url     : https://prove2.me/submissions/7ac58b4d-93ed-46ba-bea1-e2d78d09bd4c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_fin_one_fun_eq_const_141b478a75fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_mem_mcPts_9510ee445b9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2

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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
theorem _root_.solution {w : (Fin 1 → PlIdx 1 n) → ℂ} (hw : w ≠ 0) :
    blockLift (fun I => w fun _ => I) ∈ mcPts (grassIdeal 1 1 n) ∧
      segre (ι := plBlocks 1 1 n) (blockLift fun I => w fun _ => I) = w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨(mem_mcPts _).2 fun _ => ⟨i 0, ?_⟩, ?_⟩
  · simpa [blockLift, fin_one_fun_eq_const] using hi
  · rw [segre_blockLift]
    funext i'
    simp only [fin_one_fun_eq_const]
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
