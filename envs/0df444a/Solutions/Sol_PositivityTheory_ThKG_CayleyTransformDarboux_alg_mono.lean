-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.alg_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:50.665886+00:00
-- url     : https://prove2.me/submissions/694078a0-4cfe-4a8c-b021-e5da4d8912c9

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_alg_le
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_un_mem

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
theorem _root_.solution {r r' : I → I → Prop} (h : ∀ a b, r a b → r' a b) : alg ι r ≤ alg ι r' :=
  alg_le fun w a b e => un_mem w (h a b e)
end PositivityTheory.ThKG.CayleyTransformDarboux
