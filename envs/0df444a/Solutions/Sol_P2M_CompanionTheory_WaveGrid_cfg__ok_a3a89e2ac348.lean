-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_cfg__ok_a3a89e2ac348
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:31.308959+00:00
-- url     : https://prove2.me/submissions/e02ca458-ebf9-4322-96d3-a57e19331e96

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
namespace CompanionTheory.WaveGrid
theorem _root_.solution : cfg₀.Ok where
  hk := by
    norm_num [cfg₀]
  hm := by norm_num [cfg₀]
  hDel := by norm_num [cfg₀]
  hv0 := by norm_num [cfg₀]
  hv1 := by norm_num [cfg₀, Sz.Cfg.v]
  hb1 := by norm_num [cfg₀]
  hgap := by
    intro j _ _
    simp only [cfg₀]
    push_cast
    linarith
  ha := by norm_num [cfg₀, Sz.Cfg.v]
  htop := by simp [cfg₀]
end CompanionTheory.WaveGrid
