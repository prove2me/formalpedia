-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:47.848203+00:00
-- url     : https://prove2.me/submissions/55406b85-bb36-47e8-88af-c10f3d917f72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_apply_45cf6933810d

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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.TransverseSliceGeneral
theorem _root_.solution (q : Fin n → ℂ) (i : Fin n) (c : ℂ) :
    gradAt q (X i - C c) = Pi.single i 1 := by
  ext j
  by_cases h : i = j
  · subst h; simp [gradAt_apply, pderiv_X]
  · simp [gradAt_apply, pderiv_X, h, Ne.symm h]
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
