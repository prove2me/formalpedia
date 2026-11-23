-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.hermitian_isotropic_proj_complement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:37.643805+00:00
-- url     : https://prove2.me/submissions/2e51948f-80ce-4eee-9277-bbe7bebb4262

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
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h (D.pU x) w = 0 := by
  simp only [pU, LinearMap.add_apply, pX, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, h_add_left, D_h_sum_left, h_smul_left, hw.1, hw.2.1, hw.2.2, mul_zero,
    Finset.sum_const_zero, add_zero]
end PI.LevelKSplit.W.SemiG.Dat
