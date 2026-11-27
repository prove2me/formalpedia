-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_Telescoping_proof_3d108e34d8f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:03.266282+00:00
-- url     : https://prove2.me/submissions/2a26efac-0f27-4633-9bdb-6409339dd388

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
namespace Telescoping
theorem _root_.solution : Telescoping.Statement := by
  intro X _ D A R S
  refine ⟨S.teleConst, max S.ell₀ (Real.exp 1), fun t t' ht' htt hℓ x hx => ⟨?_, ?_⟩⟩
  · exact S.tele_near ht' htt (le_trans (le_max_left _ _) hℓ) (le_trans (le_max_right _ _) hℓ) hx
  · exact S.tele_far ht' htt (le_trans (le_max_left _ _) hℓ) (le_trans (le_max_right _ _) hℓ) hx
end Telescoping
end GroundTheory.Heights₂.Heights.AnalyticLimit
