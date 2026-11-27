-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFromLelong_proof_c45587746945
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:13.274171+00:00
-- url     : https://prove2.me/submissions/0d57f685-58d1-404a-bee9-c9d642353b30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionDegreeSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFromLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_of_slices_7e0cd20a7e70

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace MassFromLelong
theorem _root_.solution (hS : SliceSectionMass.Statement)
    (hA : SectionHyperplaneAvoid.Statement) (hD : SectionDegreeSum.Statement)
    (hP : PointSliceMass.Statement) : MassFromLelong.Statement :=
  fun _ _ _ _ _ hCP _ => ConeIntegralMass.of_slices hCP hS hA hD hP
end MassFromLelong
end GroundTheory.Heights₂.Heights
