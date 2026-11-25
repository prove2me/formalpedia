-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.alg_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:53.242668+00:00
-- url     : https://prove2.me/submissions/bc84825d-d4ff-4e0a-81ec-ac6b2bce87b8

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
theorem _root_.solution {r r₁ r₂ : I → I → Prop} (h : ∀ a b, r a b → r₁ a b ∨ r₂ a b) : alg ι r ≤ alg ι r₁ ⊔ alg ι r₂ :=
  alg_le fun w a b e => (h a b e).elim (fun e => Submodule.mem_sup_left (un_mem w e)) fun e =>
    Submodule.mem_sup_right (un_mem w e)
end PositivityTheory.ThKG.CayleyTransformDarboux
