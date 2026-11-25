-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_Ik_fc9667f8e9a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:33.417038+00:00
-- url     : https://prove2.me/submissions/76fc7f4d-cba0-41ac-ab21-9038b76d294a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_pk_e63cdc65944f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_Ik_le_one_c5e9977958ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_pk_pow_le_Ik_fbb0273b26eb

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (e : ℕ) : Tendsto (Ik e) atTop (𝓝 1) := by
  have hp : Tendsto (fun k => pk k ^ (e + 1)) atTop (𝓝 1) := by
    simpa using tendsto_pk.pow (e + 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds (pk_pow_le_Ik e) (Ik_le_one e)
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
