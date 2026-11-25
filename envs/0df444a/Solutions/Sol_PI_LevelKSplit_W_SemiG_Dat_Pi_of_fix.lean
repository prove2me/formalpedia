-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.Pi_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:43.032893+00:00
-- url     : https://prove2.me/submissions/5445b4cf-f0a2-489a-a4b2-278451983a5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_e_S
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_z_S
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isW_pW

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
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.Pi S v = S v := by
  have hSU : S (D.pU v) = D.pU v := by
    simp only [pU, LinearMap.add_apply, pX, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
      map_add, map_sum, map_smul, hS.1, hf, hS.2]
  have hw := isW_pW H v
  have h1 : ∀ a, D.h (D.e a) (S (D.pW v)) = 0 := fun a => by rw [h_e_S hS hU, hw.1]
  have h2 : ∀ a, D.h (D.f a) (S (D.pW v)) = 0 := fun a => by rw [← hf a, hU, hw.2.1]
  have h3 : D.h D.z (S (D.pW v)) = 0 := by rw [h_z_S hS hU, hw.2.2]
  have hpUS : D.pU (S (D.pW v)) = 0 := by
    simp only [pU, LinearMap.add_apply, pX, pXv, pz, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, hL_apply_lemma, h1, h2, h3, smul_eq_mul, mul_zero, zero_smul,
      Finset.sum_const_zero, add_zero]
  have hpW : D.pW (S (D.pW v)) = S (D.pW v) := by
    rw [show D.pW (S (D.pW v)) = S (D.pW v) - D.pU (S (D.pW v)) from rfl, hpUS, sub_zero]
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, hpW]
  rw [← hSU, ← map_add]
  congr 1
  simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
  abel
end PI.LevelKSplit.W.SemiG.Dat
