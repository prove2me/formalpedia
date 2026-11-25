-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.alg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:21:07.200958+00:00
-- url     : https://prove2.me/submissions/a2ff5d37-396c-47e0-b074-634e74cc504f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {r : I → I → Prop} {S : Submodule ℂ (ι → Matrix I I ℂ)} (h : ∀ w a b, r a b → un w a b ∈ S) : alg ι r ≤ S := by
  intro Z hZ
  rw [eq_sum Z]
  refine S.sum_mem fun w _ => S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  by_cases e : r a b
  · exact S.smul_mem _ (h w a b e)
  · rw [hZ w a b e, zero_smul]; exact S.zero_mem
end PositivityTheory.ThKG.CayleyTransformDarboux
