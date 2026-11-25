-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.alg_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:51.431366+00:00
-- url     : https://prove2.me/submissions/e3cf6264-0278-4312-825a-81c438c717d6

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
theorem _root_.solution {r : I → I → Prop} (ht : ∀ a b c, r a b → r b c → r a c) :
    ∀ X ∈ alg ι r, ∀ Y ∈ alg ι r, X * Y - Y * X ∈ alg ι r := by
  have m : ∀ X ∈ alg ι r, ∀ Y ∈ alg ι r, X * Y ∈ alg ι r := fun X hX Y hY w a b h => by
    rw [Pi.mul_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases e : r a c
    · rw [hY w c b fun e' => h (ht _ _ _ e e'), mul_zero]
    · rw [hX w a c e, zero_mul]
  exact fun X hX Y hY => sub_mem (m X hX Y hY) (m Y hY X hX)
end PositivityTheory.ThKG.CayleyTransformDarboux
