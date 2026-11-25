-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_norm_sq_split_85435cb7ec5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:57.638587+00:00
-- url     : https://prove2.me/submissions/ca63de56-d432-4a92-936b-0d69125693ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_outPart_apply_c788a3953d82

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
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentGraphLowerDensity
theorem _root_.solution {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖TangentGraphLowerDensity.inPart b I z‖ ^ 2 + ‖TangentGraphLowerDensity.outPart b I z‖ ^ 2 := by
  classical
  rw [← b.repr.norm_map z, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [TangentGraphLowerDensity.inPart_apply, TangentGraphLowerDensity.outPart_apply,
    OrthonormalBasis.repr_apply_apply]
  convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) (fun i => ‖inner ℂ (b i) z‖ ^ 2)).symm using 3
  congr 1; exact Subsingleton.elim _ _
end TangentGraphLowerDensity
end GroundTheory.Heights₂.Heights
