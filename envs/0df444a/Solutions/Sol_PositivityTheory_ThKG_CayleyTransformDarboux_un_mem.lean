-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.un_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:53.276647+00:00
-- url     : https://prove2.me/submissions/f1d14d1f-e3ab-4c16-ac5a-2727921d6a31

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
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {r : I → I → Prop} (w : ι) {a b : I} (h : r a b) : un w a b ∈ alg ι r := by
  intro w' c d hcd
  by_cases e : w' = w
  · subst e
    simp only [un, Pi.single_eq_same, Matrix.single_apply]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd h
  · simp [un, Pi.single_eq_of_ne e]
end PositivityTheory.ThKG.CayleyTransformDarboux
