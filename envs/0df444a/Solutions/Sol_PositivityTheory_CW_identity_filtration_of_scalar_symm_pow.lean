-- Prove2me | solution 1 for PositivityTheory.CW.identity_filtration_of_scalar.symm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:04.369054+00:00
-- url     : https://prove2.me/submissions/ac96f9e4-85a7-4f85-a680-2ee757e2f7ed

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SymmetricPowerHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.identity_filtration_of_scalar
namespace PositivityTheory.CW.identity_filtration_of_scalar
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (P : Module.End ℂ W)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) :
    ∀ k : ℕ, ∀ x y, inner ℂ ((P ^ k) x) y = inner ℂ x ((P ^ k) y) := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hP]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.self_pow P k).eq]
end PositivityTheory.CW.identity_filtration_of_scalar
