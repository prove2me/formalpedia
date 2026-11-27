-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_lamData_cfg__1039da455f87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:49.552802+00:00
-- url     : https://prove2.me/submissions/8ce58523-f025-48ec-89a3-2c02602f6589

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Theorems.Thm_CompanionTheory_WaveGrid_lamData_cfg
import Theorems.Thm_P2M_CompanionTheory_WaveGrid_cfg__ok_a3a89e2ac348

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
theorem _root_.solution :
    LamData (cfgPar cfg₀ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)) cfg₀.lam 10 (4 * cfg₀.Del) 400 := by
  refine lamData_cfg cfg₀ 0 (by norm_num [cfg₀]) cfg₀_ok 1 1 _ _ (fun _ => Or.inl rfl) ?_ 10 400
    (by norm_num) (by norm_num [cfg₀]) (by norm_num [cfg₀]) ?_
  · intro i
    split_ifs <;> simp
  · intro j _ hj
    simp only [cfg₀] at hj ⊢
    have : (j:ℝ) ≤ 2 := by exact_mod_cast hj
    linarith
end CompanionTheory.WaveGrid
