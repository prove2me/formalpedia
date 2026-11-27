-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ChartGlue_proof_c3b030459b35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:37.524415+00:00
-- url     : https://prove2.me/submissions/f61d2b33-0520-469c-883c-2b23abade7a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PChartGlue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_frame_f0b793a7400f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_overlap_1478a5dc89ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_B__iff_9151688a4893
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace ChartGlue
theorem _root_.solution : ChartGlue.Statement := by
  intro Ω _ _ τ _ x r E _ _ S o₀ _ _ _ _ o _ _ _ _ B₀ Bp hSR
  refine ⟨{ lat := glueLat B₀ Bp
            stable := glueLat_stable
            frame := fun i hi => glueLat_frame hi fun p => hSR p i hi
            overlap := glueLat_overlap }, fun i hi => ⟨mem_B₀_iff fun p => hSR p i hi,
              fun p v => mem_Bp_iff (fun p => hSR p i hi) p v⟩⟩
end ChartGlue
end GroundTheory.Heights₂.Heights.Model
