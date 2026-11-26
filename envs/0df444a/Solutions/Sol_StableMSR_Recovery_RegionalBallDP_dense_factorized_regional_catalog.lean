-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.dense_factorized_regional_catalog
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:15:45.724408+00:00
-- url     : https://prove2.me/submissions/39ddf0f3-9ac1-44ab-805d-4098c9e85d52

import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_disjoint_local_menus_certify_terminal
import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_dense_local_region_menu_generator
import Definitions.Def_StableMSR_LocalBallTrials
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
theorem solution : ∃a b : ℕ,0<a ∧ 0<b ∧ ∀e : ℚ,0<e → e<1 →
    ∃cmd : Cmd,∀(n k : ℕ) (d : Point n→Point n→ℝ),
      1≤k → k<n → fewBound (e:ℝ)<k → IsMetricArray d → regionalSpec e a b cmd n k d := by
  obtain ⟨a,b,ha,hb,gen⟩:=dense_local_region_menu_generator
  refine ⟨a,b,ha,hb,?_⟩
  intro e he he'
  obtain ⟨cmd,run⟩:=gen e he he'
  refine ⟨cmd,?_⟩
  intro n k d hk kn big metric
  obtain ⟨s,z,H,ez,tz,hH,ready,hs,ok⟩:=run n k d hk kn big metric
  refine ⟨s,z,H,ez,tz,hH,ready,hs,?_⟩
  intro O stable many
  obtain ⟨v,⟨trial⟩⟩:=ok O stable many
  exact ⟨v,disjoint_local_menus_certify_terminal _ hs v _ trial⟩

