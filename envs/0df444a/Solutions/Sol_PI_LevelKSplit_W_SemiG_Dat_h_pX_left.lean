-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_pX_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:19.387731+00:00
-- url     : https://prove2.me/submissions/7fe32c26-8800-41b3-bb92-2fd283ac055b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable {D : Dat A n r}
private theorem D_h_sum_left {ι : Type} (s : Finset ι) (g : ι → n → A) (y : n → A) :
    D.h (∑ a ∈ s, g a) y = ∑ a ∈ s, D.h (g a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Dat.h, hform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]
end Dat
end PI.LevelKSplit.W.SemiG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) : D.h (D.pX u) y = 0 := by
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply, D_h_sum_left, h_smul_left, hy, mul_zero,
    Finset.sum_const_zero]
end PI.LevelKSplit.W.SemiG.Dat
