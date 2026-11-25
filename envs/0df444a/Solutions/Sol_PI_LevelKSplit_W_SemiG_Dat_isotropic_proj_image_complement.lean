-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.isotropic_proj_image_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:42.115689+00:00
-- url     : https://prove2.me/submissions/ba6bd660-4a40-4e1c-9841-ce0ae793e613

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
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
private theorem hL_apply_lemma (x y : n → A) : D.hL x y = D.h x y := rfl
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
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) {w : n → A} (hw : IsW D w) :
    D.pU (S w) = D.pX (S w) := by
  simp only [pU, LinearMap.add_apply, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, hL_apply_lemma, (hW w hw).1, (hW w hw).2, smul_eq_mul, mul_zero, zero_smul,
    Finset.sum_const_zero, add_zero]
end PI.LevelKSplit.W.SemiG.Dat
