-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.low_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:02.15417+00:00
-- url     : https://prove2.me/submissions/a728cd46-f28a-4305-a30f-702cc9371304

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow

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
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {T : Module.End ℂ M} {lam : ℂ} {x : M} (h1 : x ∈ low T lam) (h2 : x ∈ T.eigenspace lam) : x = 0 := by
  have hd := (Module.End.eigenspaces_iSupIndep T) lam
  refine (Submodule.disjoint_def.1 hd) x h2 ?_
  refine (iSup_le fun t => ?_ : low T lam ≤ _) h1
  refine le_iSup₂_of_le (f := fun j (_ : j ≠ lam) => T.eigenspace j) (lam - (t.1 : ℂ)) ?_ le_rfl
  intro e
  rw [sub_eq_self] at e
  exact t.2.ne' (by exact_mod_cast e)
end PositivityTheory.ThKG.CayleyTransformDarboux
