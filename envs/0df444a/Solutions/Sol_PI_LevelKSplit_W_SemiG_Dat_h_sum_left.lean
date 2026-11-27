-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:40.162106+00:00
-- url     : https://prove2.me/submissions/6970f83c-f0cb-45e9-95f5-f4e919fb9e07

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → n → A) (y : n → A) :
    D.h (∑ i ∈ s, x i) y = ∑ i ∈ s, D.h (x i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, h_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]
end PI.LevelKSplit.W.SemiG.Dat
