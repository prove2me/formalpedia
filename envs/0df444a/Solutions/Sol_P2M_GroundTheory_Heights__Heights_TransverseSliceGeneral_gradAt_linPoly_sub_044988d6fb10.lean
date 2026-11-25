-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_linPoly_sub_044988d6fb10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:45.586107+00:00
-- url     : https://prove2.me/submissions/c20c1832-c8cf-4f61-b2fe-632930836ca5

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
theorem _root_.solution (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    gradAt q (linPoly L i - C ((L *ᵥ q) i)) = L i := by
  ext j
  simp [gradAt_apply, linPoly, pderiv_X, Pi.single_apply]
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
