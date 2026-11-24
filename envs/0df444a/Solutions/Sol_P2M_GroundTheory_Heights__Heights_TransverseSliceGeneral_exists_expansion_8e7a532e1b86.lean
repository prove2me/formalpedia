-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:15.260333+00:00
-- url     : https://prove2.me/submissions/cb5640da-5104-457c-8653-4ac13e1de8a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_UpperTheory_Reformulated_B_Qn12_exists_expansion


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
theorem _root_.solution (q : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    ∃ c : Fin n → MvPolynomial (Fin n) ℂ, p = C (eval q p) + ∑ i, c i * (X i - C (q i)) :=
  _root_.UpperTheory.Reformulated.B.Qn12.exists_expansion q p
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
