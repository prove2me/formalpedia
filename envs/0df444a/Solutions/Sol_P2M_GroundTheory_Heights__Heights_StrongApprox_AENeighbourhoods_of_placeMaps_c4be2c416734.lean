-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_of_placeMaps_c4be2c416734
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:39.145086+00:00
-- url     : https://prove2.me/submissions/c8582518-16fd-41c7-a10b-c737550f4c03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_int_cofinite_824d33c90484
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_nhds_of_sep_e7517c82270c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution (hP : PlaceMaps.Statement) : AENeighbourhoods.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  exact ⟨fun N U hU => nhds_of_sep (hP F E c h2 hc).1 N U hU, int_cofinite⟩
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
